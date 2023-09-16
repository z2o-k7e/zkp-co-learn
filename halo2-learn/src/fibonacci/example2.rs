use std::marker::PhantomData;
use ff::{Field, PrimeField};
use halo2_proofs::{circuit::*, plonk::*, poly::Rotation};

#[derive(Debug, Clone)]
struct ACell<F: PrimeField>(AssignedCell<F, F>);

#[derive(Debug, Clone)]
struct FiboConfig {
    advice: Column<Advice>,
    selector: Selector,
    instance: Column<Instance>,
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
        advice: Column<Advice>,
        instance: Column<Instance>,
    ) -> FiboConfig {
        let selector = meta.selector();

        meta.enable_equality(advice);
        meta.enable_equality(instance);
        
        // Gen Custom Gate:
        // - `Rotation::cur()`  当前行 
        // - `Rotation::next()`  下一行
        // - `Rotation(2)`  再下一行
        meta.create_gate("add", |meta| {
            //
            // advice | selector
            //   a    |   s
            //   b    |
            //   c    |
            //
            let s = meta.query_selector(selector);
            let a = meta.query_advice(advice, Rotation::cur());
            let b = meta.query_advice(advice, Rotation::next());
            let c = meta.query_advice(advice, Rotation(2));
            vec![s * (a + b - c)]
        });

        FiboConfig {
            advice,
            selector,
            instance,
        }
    }

    pub fn assign(
        &self,
        mut layouter: impl Layouter<F>,
        nrows: usize,  // 前 2 列赋值之后, 后面要搞的列数.. 
    ) -> Result<ACell<F>, Error> {
        layouter.assign_region(
            || "entire fibonacci table",
            |mut region| {
                // 为前两行启用 selector, 这意味着我们将从 instance (public input) 列中复制 Fibo 序列的前 2 个数字
                self.config.selector.enable(&mut region, 0)?;
                self.config.selector.enable(&mut region, 1)?;
                
                // assign_advice_from_instance 方法，将 instance (public input) 列的前 2 个值
                //   (即 Fibonacci 序列的前两个数字）赋给 advice 列中的前 2 个单元格
                //   后面在 MockProver 中, 我们会传入 instance 作为 Public input
                let mut a_cell = region.assign_advice_from_instance(
                    || "1",
                    self.config.instance,
                    0,  // instance column's row 0
                    self.config.advice,
                    0, // 复制到当前的 region 的 row 0
                ).map(ACell)?;

                let mut b_cell = region.assign_advice_from_instance(
                    || "1",
                    self.config.instance,
                    1, // instance column's row 1
                    self.config.advice,
                    1,  // 复制到当前的 region 的 row 1
                ).map(ACell)?;

                // 赋值好了前 2 行(递归基), 其余的行就累加过去就好了
                for row in 2..nrows { // 对于最后两行, 不需要启用 Selector
                    if row < nrows - 2 {
                        self.config.selector.enable(&mut region, row)?;
                    }

                    let c_cell = region.assign_advice(
                        || "advice",
                        self.config.advice,
                        row,
                        || a_cell.0.value().copied() + b_cell.0.value(),
                    ).map(ACell)?;

                    a_cell = b_cell; // let mut a_cell ...
                    b_cell = c_cell;
                }

                Ok(b_cell) // return the last cell.
            },
        )
    }

    pub fn expose_public(
        &self,
        mut layouter: impl Layouter<F>,
        cell: ACell<F>,
        row: usize,
    ) -> Result<(), Error> {
        layouter.constrain_instance(cell.0.cell(), self.config.instance, row)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use halo2_proofs::{dev::MockProver, pasta::Fp};

    #[derive(Default)]
    struct MyCircuit<F>(PhantomData<F>);

    impl<F: PrimeField> Circuit<F> for MyCircuit<F> {
        type Config = FiboConfig;
        type FloorPlanner = SimpleFloorPlanner;

        fn without_witnesses(&self) -> Self {
            Self::default()
        }

        fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
            let advice = meta.advice_column();
            let instance = meta.instance_column();
            FiboChip::configure(meta, advice, instance)
        }

        fn synthesize(
            &self,
            config: Self::Config,
            mut layouter: impl Layouter<F>,
        ) -> Result<(), Error> {
            let chip = FiboChip::construct(config);
            
            // entire table's last cell is the output of 10 times Fibonacci.
            let out_cell = chip.assign(layouter.namespace(|| "entire table"), 10)?;

            chip.expose_public(layouter.namespace(|| "out"), out_cell, 2)?;

            Ok(())
        }
    }

    #[test]
    fn test_example2() {
        let k = 4;

        let a = Fp::from(1); // F[0]
        let b = Fp::from(1); // F[1]
        let out = Fp::from(55); // F[9]

        let circuit = MyCircuit(PhantomData);

        let mut public_input = vec![a, b, out];

        let prover = MockProver::run(k, &circuit, vec![public_input.clone()]).unwrap();
        prover.assert_satisfied();

        public_input[2] += Fp::one();
        let _prover = MockProver::run(k, &circuit, vec![public_input]).unwrap();
        // uncomment the following line and the assert will fail
        // _prover.assert_satisfied();
    }

    // $ cargo test --release --all-features plot_fibo2
    #[cfg(feature = "dev-graph")]
    #[test]
    fn plot_fibo2() {
        use plotters::prelude::*;
        let root = BitMapBackend::new("fib-2-layout.png", (1024, 3096)).into_drawing_area();
        root.fill(&WHITE).unwrap();
        let root = root.titled("Fib 2 Layout", ("sans-serif", 60)).unwrap();

        let circuit = MyCircuit::<Fp>(PhantomData);
        halo2_proofs::dev::CircuitLayout::default()
            .render(4, &circuit, &root)
            .unwrap();
    }
}