use std::marker::PhantomData;
use ff::{Field, PrimeField};
use halo2_proofs::{circuit::*, plonk::*, poly::Rotation};

#[derive(Debug, Clone)]
struct ACell<F: PrimeField>(AssignedCell<F, F>);

#[derive(Debug, Clone)]
struct FiboConfig {
    pub advice: [Column<Advice>; 3],
    pub selector: Selector,
    pub instance: Column<Instance>,
}

#[derive(Debug, Clone)]
struct FiboChip<F: PrimeField> {
    config: FiboConfig,
    _marker: PhantomData<F>,
}

impl<F: PrimeField> FiboChip<F> {
    pub fn construct(config: FiboConfig) -> Self {
        Self {
            config,
            _marker: PhantomData,
        }
    }

    pub fn configure(
        meta: &mut ConstraintSystem<F>,
        advice: [Column<Advice>; 3],
        instance: Column<Instance>,
    ) -> FiboConfig {
        let col_a = advice[0]; // 对每个 advice 列进行命名
        let col_b = advice[1];
        let col_c = advice[2];
        let selector = meta.selector();

        meta.enable_equality(col_a);
        meta.enable_equality(col_b);
        meta.enable_equality(col_c);
        meta.enable_equality(instance);

        meta.create_gate("add", |meta| {
            //
            // col_a | col_b | col_c | selector
            //   a      b        c       s

            // Query a selector at the current position.
            let s = meta.query_selector(selector);
            // if Rotation::next`  means  `ωx`, 这 3 列都在同一行, 所以都是 Rotation::cur()
            // 除了 Rotation::cur() 之外, 还有 Rotation::prev 和 Rotation::next 
            let a = meta.query_advice(col_a, Rotation::cur());
            let b = meta.query_advice(col_b, Rotation::cur());
            let c = meta.query_advice(col_c, Rotation::cur());
            // need s * (a + b - c) == 0
            vec![s * (a + b - c)]
        });

        FiboConfig {
            advice: [col_a, col_b, col_c],
            selector,
            instance,
        }
    }

    #[allow(clippy::type_complexity)]
    pub fn assign_first_row(
        &self,
        mut layouter: impl Layouter<F>,
    ) -> Result<(ACell<F>, ACell<F>, ACell<F>), Error> {
        layouter.assign_region(
            || "first row",
            |mut region| {
                self.config.selector.enable(&mut region, 0)?;

                let a_cell = region.assign_advice_from_instance(
                    || "f(0)",
                    self.config.instance,
                    0, // instance column's row 0
                    self.config.advice[0],
                    0  // offset, advice column's row.
                ).map(ACell)?;

                let b_cell = region.assign_advice_from_instance(
                    || "f(1)",
                    self.config.instance,
                    1, // instance column's row 1
                    self.config.advice[1],
                    0   // offset, advice column's row.
                ).map(ACell)?;

                let c_cell = region.assign_advice(
                    || "f(0)+f(1) i.e. a + b",
                    self.config.advice[2],
                    0,
                    || a_cell.0.value().copied() + b_cell.0.value()
                ).map(ACell)?;

                Ok((a_cell, b_cell, c_cell))
            },
        )
    }

    pub fn assign_row(
        &self,  // 当前`FiboChip`实例的引用
        mut layouter: impl Layouter<F>,
        prev_b: &ACell<F>,   // Fibonacci 数列中的上一行的第 2/3 个 Advice Cell
        prev_c: &ACell<F>,
    ) -> Result<ACell<F>, Error> {
        layouter.assign_region(
            || "next row",
            |mut region| {
                self.config.selector.enable(&mut region, 0)?;

                prev_b.0.copy_advice(
                    || "a", 
                    &mut region, 
                    self.config.advice[0], 
                    0
                )?;
                prev_c.0.copy_advice(|| "b", &mut region, self.config.advice[1], 0)?;

                let c_val = prev_b.0.value().copied() + prev_c.0.value();

                let c_cell = region
                    .assign_advice(|| "c", self.config.advice[2], 0, || c_val)
                    .map(ACell)?;

                Ok(c_cell)
            },
        )
    }

    pub fn expose_public(
        &self,
        mut layouter: impl Layouter<F>,
        cell: &ACell<F>,
        row: usize,
    ) -> Result<(), Error> {
        layouter.constrain_instance(cell.0.cell(), self.config.instance, row)
    }
}

#[derive(Default)]
struct MyCircuit<F> (PhantomData<F>);

impl<F: PrimeField> Circuit<F> for MyCircuit<F> {
    type Config = FiboConfig;
    type FloorPlanner = SimpleFloorPlanner;

    fn without_witnesses(&self) -> Self {
        Self::default()
    }

    fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
        let col_a = meta.advice_column();
        let col_b = meta.advice_column();
        let col_c = meta.advice_column();
        let instance = meta.instance_column();
        FiboChip::configure(meta, [col_a, col_b, col_c], instance)
    }

    fn synthesize(
        &self,
        config: Self::Config,
        mut layouter: impl Layouter<F>,
    ) -> Result<(), Error> {
        let chip = FiboChip::construct(config);

        let (_, mut prev_b, mut prev_c) =
            chip.assign_first_row(layouter.namespace(|| "first row"))?;
        
        // 这是干啥??
        // chip.expose_public(layouter.namespace(|| "private a"), &prev_a, 0)?;
        // chip.expose_public(layouter.namespace(|| "private b"), &prev_b, 1)?;

        for _i in 3..10 {
            let c_cell = chip.assign_row(layouter.namespace(|| "next row"), &prev_b, &prev_c)?;
            prev_b = prev_c;
            prev_c = c_cell;
        }

        chip.expose_public(layouter.namespace(|| "out"), &prev_c, 2)?;

        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::MyCircuit;
    use halo2_proofs::{circuit::Value, dev::MockProver, pasta::Fp};
    use std::marker::PhantomData;

    #[test]
    fn test_example1() {
        let k = 4;

        let a = Fp::from(1); // F[0]
        let b = Fp::from(1); // F[1]
        let out = Fp::from(55); // F[9]

        let circuit = MyCircuit(PhantomData);

        let mut public_input = vec![a, b, out];

        let prover = MockProver::run(k, &circuit, vec![public_input.clone()]).unwrap();
        prover.assert_satisfied();

        public_input[2] += Fp::one(); // out += 2  =>  unsatisfied
        let _prover = MockProver::run(k, &circuit, vec![public_input]).unwrap();
        // uncomment the following line and the assert will fail
        // _prover.assert_satisfied();
    }

    // $ cargo test --release --all-features plot_fibo1
    #[cfg(feature = "dev-graph")]
    #[test]
    fn plot_fibo1() {
        use plotters::prelude::*;

        let root = BitMapBackend::new("fib-1-layout.png", (1024, 3096)).into_drawing_area();
        root.fill(&WHITE).unwrap();
        let root = root.titled("Fib 1 Layout", ("sans-serif", 60)).unwrap();

        let circuit = MyCircuit::<Fp>(PhantomData);
        halo2_proofs::dev::CircuitLayout::default()
            .render(4, &circuit, &root)
            .unwrap();
    }
}