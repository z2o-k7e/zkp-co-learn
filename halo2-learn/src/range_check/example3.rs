use ff::{Field, PrimeField};
use halo2_proofs::{
    circuit::{AssignedCell, Layouter, Value},
    plonk::{Advice, Assigned, Column, ConstraintSystem, Error, Expression, Selector},
    poly::Rotation,
};

// create a submodule which is my table and use that
mod table;
use table::*;

// /// This helper uses a lookup table to check that the value witnessed in a given cell is
// /// within a given range.
// ///
// /// The lookup table is tagged by `num_bits` to give a strict range check.
// ///
// ///        value     |   q_lookup  |  table_num_bits  | lookup table_value  |
// ///       -------------------------------------------------------------
// ///          v_0     |      0      |        1         |       0       |
// ///          v_1     |      1      |        1         |       1       |
// ///          ...     |     ...     |        2         |       2       |
// ///          ...     |     ...     |        2         |       3       |
// ///          ...     |     ...     |        3         |       4       |
// ///
// /// We use a K-bit lookup table, that is tagged 1..=K, where the tag `i` marks an `i`-bit value.
// ///

#[derive(Debug, Clone)]
/// A range-constrained value in the circuit produced by the RangeCheckConfig.
struct RangeConstrained<F: PrimeField> {
    num_bits: AssignedCell<Assigned<F>, F>,
    assigned_cell: AssignedCell<Assigned<F>, F>,
}

#[derive(Debug, Clone)]
// WE ADD A FURTHER NUM_BITS COLUMN TO OUR CONFIG
struct RangeCheckConfig<F: PrimeField, const NUM_BITS: usize, const RANGE: usize> {
    q_lookup: Selector,
    num_bits: Column<Advice>,
    value: Column<Advice>,
    table: RangeTableConfig<F, NUM_BITS, RANGE>,
}

// Write the gate for our range check Config
// It's good practive to pass advice columns to the config (rather than creating it within the config)
// because these are very likely to be shared across multiple config
impl<F: PrimeField, const NUM_BITS: usize, const RANGE: usize> RangeCheckConfig<F, NUM_BITS, RANGE> {
    // REMEMBER THAT THE CONFIGURATION HAPPEN AT KEYGEN TIME
    pub fn configure(
        meta: &mut ConstraintSystem<F>,
        num_bits: Column<Advice>,
        value: Column<Advice>,
    ) -> Self {
        let q_lookup = meta.complex_selector();
        let table = RangeTableConfig::configure(meta);

        meta.lookup(|meta| {
            let q_lookup = meta.query_selector(q_lookup);
            let num_bits = meta.query_advice(num_bits, Rotation::cur());
            let value = meta.query_advice(value, Rotation::cur());

            // q_lookup = 1, not_q_lookup = 0 ; q_lookup = 0, not_q_lookup = 1
            let not_q_lookup = Expression::Constant(F::ONE ) - q_lookup.clone();
            let default_num_bits = Expression::Constant(F::ONE); // 1-bit
            let default_value = Expression::Constant(F::ZERO); // 0 is a 1-bit value
 
            // default_num_bits / default_value only used when `q_lookup` is not active.
            let num_bits_expr =
                q_lookup.clone() * num_bits + not_q_lookup.clone() * default_num_bits;
            let value_expr = q_lookup * value + not_q_lookup * default_value;

            // When q_lookup is active, the circuit will use the actual advice values, 
            //   but when it's not, the circuit will use the default values.
            // what does it mean ????? 
            vec![(num_bits_expr, table.num_bits), (value_expr, table.value)]

            // This is `num_bits` when q_lookup = 1
            // and `default_num_bits` when not_q_lookup=1 

            // THIS IS BROKEN!!!!!!
            // Hint: consider the case where q_lookup = 0. What are our input expressions to the lookup argument then?
            // vec![
            //     (q_lookup.clone() * num_bits, table.num_bits),
            //     (q_lookup * value, table.value),
            // ]

            // when q_lookup = 0, we lookup(0,0), but we WANT (1,0)
            // Solution: looks up (num_bits, value) = (1, 0) when q_lookup = 0.
        }); 

        Self {
            q_lookup,
            num_bits,
            value,
            table,
        }
    }

    pub fn assign(
        &self,
        mut layouter: impl Layouter<F>,
        num_bits: Value<u8>,
        value: Value<Assigned<F>>,
    ) -> Result<RangeConstrained<F>, Error> {
        layouter.assign_region(
            || "Assign value",
            |mut region| {
                let offset = 0;

                // Enable q_lookup
                self.q_lookup.enable(&mut region, offset)?;

                // Assign num_bits
                let num_bits = num_bits.map(|v| F::from(v as u64));
                let num_bits = region.assign_advice(
                    || "num_bits",
                    self.num_bits,
                    offset,
                    || num_bits.into(),
                )?;

                // Assign value
                let assigned_cell =
                    region.assign_advice(|| "value", self.value, offset, || value)?;

                Ok(RangeConstrained {
                    num_bits,
                    assigned_cell,
                })
            },
        )
    }
}

#[cfg(test)]
mod tests {
    use halo2_proofs::{circuit::floor_planner::V1, dev::MockProver, pasta::Fp, plonk::Circuit};

    use super::*;

    #[derive(Default)]
    struct MyCircuit<F: PrimeField, const NUM_BITS: usize, const RANGE: usize> {
        num_bits: Value<u8>,
        value: Value<Assigned<F>>,
    }

    impl<F: PrimeField, const NUM_BITS: usize, const RANGE: usize> Circuit<F>
        for MyCircuit<F, NUM_BITS, RANGE>
    {
        type Config = RangeCheckConfig<F, NUM_BITS, RANGE>;
        type FloorPlanner = V1;

        fn without_witnesses(&self) -> Self {
            Self::default()
        }

        fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
            let num_bits = meta.advice_column();
            let value = meta.advice_column();
            RangeCheckConfig::configure(meta, num_bits, value)
        }

        fn synthesize(
            &self,
            config: Self::Config,
            mut layouter: impl Layouter<F>,
        ) -> Result<(), Error> {
            config.table.load(&mut layouter)?;

            config.assign(
                layouter.namespace(|| "Assign value"),
                self.num_bits,
                self.value,
            )?;

            Ok(())
        }
    }

    #[test]
    fn test_range_check_3() {
        let k = 9;
        const NUM_BITS: usize = 8;
        const RANGE: usize = 256; // 8-bit value

        // Successful cases
        for num_bits in 1u8..=NUM_BITS.try_into().unwrap() {
            for value in (1 << (num_bits - 1))..(1 << num_bits) {
                let circuit = MyCircuit::<Fp, NUM_BITS, RANGE> {
                    num_bits: Value::known(num_bits),
                    value: Value::known(Fp::from(value as u64).into()),
                };

                let prover = MockProver::run(k, &circuit, vec![]).unwrap();
                prover.assert_satisfied();
            }
        }
    }

    // $ cargo test --release --all-features print_range_check_3
    #[cfg(feature = "dev-graph")]
    #[test]
    fn print_range_check_3() {
        use plotters::prelude::*;

        let root = BitMapBackend::new("range-check-3-layout.png", (1024, 3096)).into_drawing_area();
        root.fill(&WHITE).unwrap();
        let root = root
            .titled("Range Check 3 Layout", ("sans-serif", 60))
            .unwrap();

        let circuit = MyCircuit::<Fp, 8, 256> {
            num_bits: Value::unknown(),
            value: Value::unknown(),
        };
        halo2_proofs::dev::CircuitLayout::default()
            .render(9, &circuit, &root)
            .unwrap();
    }
}
