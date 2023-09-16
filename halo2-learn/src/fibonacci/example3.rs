use crate::is_zero::{IsZeroChip, IsZeroConfig};
use ff::{Field, PrimeField};
use halo2_proofs::{
    circuit::{AssignedCell, Layouter, SimpleFloorPlanner, Value},
    plonk::{Advice, Circuit, Column, ConstraintSystem, Error, Expression, Selector},
    poly::Rotation,
};

#[derive(Debug, Clone)]
struct FunctionConfig<F: PrimeField> {
    selector: Selector,
    a: Column<Advice>,
    b: Column<Advice>,
    c: Column<Advice>,
    a_equals_b: IsZeroConfig<F>,
    output: Column<Advice>,
}

#[derive(Debug, Clone)]
struct FunctionChip<F: PrimeField> {
    config: FunctionConfig<F>,
}

impl<F: PrimeField> FunctionChip<F> {
    pub fn construct(config: FunctionConfig<F>) -> Self {
        Self { config }
    }

    pub fn configure(meta: &mut ConstraintSystem<F>) -> FunctionConfig<F> {
        let selector = meta.selector();
        let a = meta.advice_column();
        let b = meta.advice_column();
        let c = meta.advice_column();
        let output = meta.advice_column();

        let is_zero_advice_column = meta.advice_column();

        // apply on column, not cell ; cell's assignments base on `fn assign()`
        //   returns IsZeroConfig<F>
        let a_equals_b: IsZeroConfig<F> = IsZeroChip::configure(
            meta,
            |meta| meta.query_selector(selector),
            |meta| meta.query_advice(a, Rotation::cur()) - meta.query_advice(b, Rotation::cur()),
            is_zero_advice_column,
        );

        meta.create_gate("f(a, b, c) = if a == b {c} else {a - b}", |meta| {
            let sel = meta.query_selector(selector);
            let a = meta.query_advice(a, Rotation::cur());
            let b = meta.query_advice(b, Rotation::cur());
            let c = meta.query_advice(c, Rotation::cur());
            let output = meta.query_advice(output, Rotation::cur());
            
            // both constrants need to be satisfied. (both need equal to 0)
            vec![
                sel.clone() * (a_equals_b.expr() * (output.clone() - c)),
                sel * (Expression::Constant(F::ONE) - a_equals_b.expr()) * (output - (a - b)),
            ]
        });

        FunctionConfig {
            selector,
            a,
            b,
            c,
            a_equals_b,
            output,
        }
    }

    pub fn assign(
        &self,
        mut layouter: impl Layouter<F>,
        a: F,
        b: F,
        c: F,
    ) -> Result<AssignedCell<F, F>, Error> {
        let is_zero_chip = IsZeroChip::construct(self.config.a_equals_b.clone());

        layouter.assign_region(
            || "f(a, b, c) = if a == b {c} else {a - b}",
            |mut region| {
                self.config.selector.enable(&mut region, 0)?;
                region.assign_advice(|| "a", self.config.a, 0, || Value::known(a))?;
                region.assign_advice(|| "b", self.config.b, 0, || Value::known(b))?;
                region.assign_advice(|| "c", self.config.c, 0, || Value::known(c))?;

                // 使用 IsZeroChip 子电路来检查 a - b 是否为零, 从而判断 `a ?= b`
                is_zero_chip.assign(&mut region, 0, Value::known(a - b))?;

                let output = if a == b { c } else { a - b }; // Rust expr to calculate val.
                region.assign_advice(|| "output", self.config.output, 0, || Value::known(output))
            },
        )
    }
}

#[derive(Default)]
struct FunctionCircuit<F> {
    a: F,
    b: F,
    c: F,
}

impl<F: PrimeField> Circuit<F> for FunctionCircuit<F> {
    type Config = FunctionConfig<F>;
    type FloorPlanner = SimpleFloorPlanner;

    fn without_witnesses(&self) -> Self {
        Self::default()
    }

    fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
        FunctionChip::configure(meta)
    }

    fn synthesize(&self, config: Self::Config, layouter: impl Layouter<F>) -> Result<(), Error> {
        let chip = FunctionChip::construct(config);
        chip.assign(layouter, self.a, self.b, self.c)?;
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use halo2_proofs::{dev::MockProver, pasta::Fp};

    #[test]
    fn test_example3() {
        let circuit = FunctionCircuit {
            a: Fp::from(10),
            b: Fp::from(12),
            c: Fp::from(15),
        };

        let prover = MockProver::run(4, &circuit, vec![]).unwrap();
        prover.assert_satisfied();
    }

    // $ cargo test --release --all-features plot_fibo3
    #[cfg(feature = "dev-graph")]
    #[test]
    fn plot_fibo3() {
        use plotters::prelude::*;
        let root = BitMapBackend::new("fib-3-layout.png", (1024, 3096)).into_drawing_area();
        root.fill(&WHITE).unwrap();
        let root = root.titled("Fib 3 Layout", ("sans-serif", 60)).unwrap();

        // let circuit = MyCircuit::<Fp> {
        //     a: Value::unknown(),
        //     b: Value::unknown(),
        // };
        // halo2_proofs::dev::CircuitLayout::default()
        //     .render(4, &circuit, &root)
        //     .unwrap();

        let circuit = FunctionCircuit::<Fp>{
            a: Fp::ZERO,
            b: Fp::ZERO,
            c: Fp::ZERO,
        };
        halo2_proofs::dev::CircuitLayout::default()
            .render(4, &circuit, &root)
            .unwrap();
    }
}
