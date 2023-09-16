use ff::{Field, PrimeField};
use halo2_proofs::{
    circuit::{AssignedCell, Layouter, SimpleFloorPlanner, Value},
    plonk::{
        Advice, Assigned, Circuit, Column, ConstraintSystem, Constraints, Error, Expression,
        Selector,
    },
    poly::Rotation,
};
use std::marker::PhantomData;

// create a submodule which is my table and use that
mod table;
use table::*;

/// Decomposes an $n$-bit Primefield element $\alpha$ into $W$ windows, each window
/// being a $K$-bit word, using a running sum $z$.
/// We constrain $K \leq 3$ for this helper.
///     $$\alpha = k_0 + (2^K) k_1 + (2^{2K}) k_2 + ... + (2^{(W-1)K}) k_{W-1}$$
///
/// $z_0$ is initialized as $\alpha$. Each successive $z_{i+1}$ is computed as
///                $$z_{i+1} = (z_{i} - k_i) / (2^K).$$
/// $z_W$ is constrained to be zero.
/// The difference between each interstitial running sum output is constrained
/// to be $K$ bits, i.e.
///                      `range_check`($k_i$, $2^K$),
/// where
/// ```text
///   range_check(word)
///     = word * (1 - word) * (2 - word) * ... * ((range - 1) - word)
/// ```
///
/// Given that the `range_check` constraint will be toggled by a selector, in
/// practice we will have a `selector * range_check(word)` expression
/// of degree `range + 1`.
///
/// This means that $2^K$ has to be at most `degree_bound - 1` in order for
/// the range check constraint to stay within the degree bound.
///
/// This is a custom built version of the decompose running sum function.

#[derive(Debug, Clone)]
/// A range-constrained value in the circuit produced by the DecomposeRangeCheckConfig.
struct RangeConstrained<F: PrimeField>(AssignedCell<F, F>);

// RANGE is the size of the total range we want to check.
// LOOKUP_RANGE is the size of our lookup table i.e. the max size we can lookup in one check to the table.
// NUM_BITS is the max number of bits we want to use to represent each value in the lookup range.
const RANGE: usize = 64;
const NUM_BITS: usize = 3;
const LOOKUP_RANGE: usize = 8;
// Thus, here we decompose a number into 3-bit chunks.

#[derive(Debug, Clone)]
struct DecomposeRangeCheckConfig<F: PrimeField> {
    value: Column<Advice>,
    value_decomposed: Column<Advice>, // Assume this value perfectly decomposes
    q_decomposed: Selector,
    q_range_check: Selector,
    table: RangeTableConfig<F, LOOKUP_RANGE>,
    _marker: PhantomData<F>,
}

impl<F: PrimeField> DecomposeRangeCheckConfig<F> {
    pub fn configure(meta: &mut ConstraintSystem<F>) -> Self {
        let value = meta.advice_column();
        let value_decomposed = meta.advice_column();
        let q_decomposed = meta.selector();
        let q_range_check = meta.complex_selector();
        let table = RangeTableConfig::configure(meta);
        //        value     |  value_decomposed |    q_decomposed      |   q_range_check   | range_check_table
        //       ---------------------------------------------------------------------------------------------
        //          v       |         v_0       |          1           |         1         |        0
        //          -       |         v_1       |          0           |         1         |        1
        //          -       |         v_2       |          0           |         1         |        2

        // Lookup each decomposed value individually, not paying attention to bit count
        meta.lookup(|meta| {
            let q = meta.query_selector(q_range_check);
            let decomposed_value = meta.query_advice(value_decomposed, Rotation::cur());
            vec![(q.clone() * decomposed_value, table.value)]
        });

        // Ensure that the decomposed values add up to the original value
        meta.create_gate("decompose", |meta| {
            let q = meta.query_selector(q_decomposed);
            let value = meta.query_advice(value, Rotation::cur());
            let mut decomposed_values = vec![];
            let decomposed_parts = RANGE / LOOKUP_RANGE;

            // Because we rotate up to 8 times here, this gate adds a lot of overhead.
            // It would be much more efficient to also have a prefix sum at each step,
            // and only cover 1-2 different rotations instead per constraint
            for i in 0..decomposed_parts {
                decomposed_values.push(meta.query_advice(value_decomposed, Rotation(i as i32)));
            }

            // Combines the decomposed values into a single value and asserts equality
            let decomposed_check =
                |decomposed_parts: usize,
                 value: Expression<F>,
                 decomposed_values: Vec<Expression<F>>| {
                    assert!(decomposed_parts > 0, "Empty value!");
                    assert!(
                        NUM_BITS * decomposed_parts < 64,
                        "Value doesn't fit in bits!"
                    );
                    const multiplier: usize = 1 << NUM_BITS;
                    (0..decomposed_parts).fold(
                        Expression::Constant(F::from(0 as u64)),
                        |expr, i| {
                            expr + decomposed_values[i].clone()
                                * Expression::Constant(F::from(1_u64 << (NUM_BITS * i)))
                        },
                    ) - value
                };

            Constraints::with_selector(
                q,
                [(
                    "range check",
                    decomposed_check(decomposed_parts, value, decomposed_values),
                )],
            )
        });

        Self {
            value,
            value_decomposed,
            q_decomposed,
            q_range_check,
            table,
            _marker: PhantomData,
        }
    }

    // Note that the two types of region.assign_advice calls happen together so that it is the same region
    pub fn assign_value(&self, mut layouter: impl Layouter<F>, value: u128) -> Result<bool, Error> {
        layouter.assign_region(
            || "Assign value",
            |mut region| {
                let offset = 0;

                // Enable q_range_check
                self.q_decomposed.enable(&mut region, offset)?;

                // Assign value
                region.assign_advice(
                    || "value",
                    self.value,
                    offset,
                    || Value::known(F::from_u128(value)),
                )?;

                // Enable q_decomposed
                let decomposed_parts = RANGE / LOOKUP_RANGE;
                let mut decompose_in_progress = value;
                for i in 0..decomposed_parts {
                    // offset = i;
                    self.q_range_check.enable(&mut region, i)?;
                    let decomposed_val = decompose_in_progress % { 1 << (i * NUM_BITS) };
                    region.assign_advice(
                        || format!("decomposed_value {:?}", i),
                        self.value_decomposed,
                        i,
                        || Value::known(F::from_u128(decomposed_val)),
                    )?;
                    decompose_in_progress = decompose_in_progress >> (i * NUM_BITS);
                }
                Ok(true)
            },
        )
    }
}
#[derive(Default, Clone)]
struct DecomposeRangeCheckCircuit<F: PrimeField> {
    // Since this is only relevant for the witness, we can opt to make this whatever convenient type we want
    pub value: u128,
    _marker: PhantomData<F>,
}

impl<F: PrimeField> Circuit<F> for DecomposeRangeCheckCircuit<F> {
    type Config = DecomposeRangeCheckConfig<F>;
    type FloorPlanner = SimpleFloorPlanner;

    // Circuit without witnesses, called only during key generation
    fn without_witnesses(&self) -> Self {
        Self {
            value: 0,
            _marker: PhantomData,
        }
    }

    fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
        let config = DecomposeRangeCheckConfig::configure(meta);
        config
    }

    fn synthesize(
        &self,
        config: Self::Config,
        mut layouter: impl Layouter<F>,
    ) -> Result<(), Error> {
        config.table.load(&mut layouter)?;
        print!("Synthesize being called...\n");
        assert!(
            RANGE % LOOKUP_RANGE == 0,
            "Range must be a multiple of lookup range"
        );
        let mut value = config.assign_value(layouter.namespace(|| "Assign all values"), self.value);
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use halo2_proofs::{
        circuit::floor_planner::V1,
        dev::{FailureLocation, MockProver, VerifyFailure},
        pasta::Fp,
        plonk::{Any, Circuit},
    };

    use super::*;

    #[test]
    fn test_range_check_pass() {
        let k = 10; // 8, 128, etc

        // Successful cases
        for i in 0..RANGE {
            let i = 0;
            let circuit = DecomposeRangeCheckCircuit::<Fp> {
                value: i as u128,
                _marker: PhantomData,
            };

            let prover = MockProver::run(k, &circuit, vec![]).unwrap();
            prover.assert_satisfied();
        }
    }

    #[test]
    fn test_range_check_fail() {
        let k = 10;
        // Out-of-range `value = 8`
        let circuit = DecomposeRangeCheckCircuit::<Fp> {
            value: RANGE as u128,
            _marker: PhantomData,
        };
        let prover = MockProver::run(k, &circuit, vec![]).unwrap();
        match prover.verify() {
            Err(e) => {
                println!("Error successfully achieved!");
            }
            _ => assert_eq!(1, 0),
        }
    }

    // $ cargo test --release --all-features print_decompose_range_check_1
    #[cfg(feature = "dev-graph")]
    #[test]
    fn print_decompose_range_check_1() {
        use plotters::prelude::*;

        let root = BitMapBackend::new("range-check-decomposed-layout.png", (1024, 3096))
            .into_drawing_area();
        root.fill(&WHITE).unwrap();
        let root = root
            .titled("Range Check 1 Layout", ("sans-serif", 60))
            .unwrap();

        let circuit = DecomposeRangeCheckCircuit::<Fp> {
            value: 2 as u128,
            _marker: PhantomData,
        };
        halo2_proofs::dev::CircuitLayout::default()
            .render(3, &circuit, &root)
            .unwrap();
    }
}