use ff::{Field, PrimeField};
use halo2_proofs::{
    circuit::{AssignedCell, Layouter, Value},
    plonk::{Advice, Assigned, Column, ConstraintSystem, Constraints, Error, Expression, Selector},
    poly::Rotation,
};

mod table;
use table::*;

// This helper checks that the value witnessed in a given cell is within a given range.
// Depending on the range, this helper uses either a range-check expression (for small ranges),
// or a lookup (for large ranges).
//
//        value     |    q_range_check    |   q_lookup  |  table_value  |
//       ----------------------------------------------------------------
//          v_0     |         1           |      0      |       0       |
//          v_1     |         0           |      1      |       1       |
//


#[derive(Debug, Clone)]
/// A range-constrained value in the circuit produced by the RangeCheckConfig.
struct RangeConstrained<F: PrimeField, const RANGE: usize>(AssignedCell<Assigned<F>, F>);

#[derive(Debug, Clone)]
struct RangeCheckConfig<F: PrimeField, const RANGE: usize, const LOOKUP_RANGE: usize> {
    q_range_check: Selector,
    q_lookup: Selector,
    value: Column<Advice>,
    table: RangeTableConfig<F, LOOKUP_RANGE>,  // Lookup table
}

// Write the gate for our range check Config
// It's good practive to pass advice columns to the config (rather than creating it within the config)
// because these are very likely to be shared across multiple config
impl<F: PrimeField, const RANGE: usize, const LOOKUP_RANGE: usize>
    RangeCheckConfig<F, RANGE, LOOKUP_RANGE>
{
    // Remember that the configuration happen at keygen time.
    pub fn configure(meta: &mut ConstraintSystem<F>, value: Column<Advice>) -> Self {
        // Toggles the range_check constraint
        let q_range_check = meta.selector();
        // Toggles the lookup argument
        let q_lookup = meta.complex_selector(); // for lookup table
        // configure a lookup table. and **pass it to config**
        let table = RangeTableConfig::configure(meta);

        // later we will return this config.
        let config = Self {
            q_range_check,
            q_lookup,
            value,
            table: table.clone()
        }; 

        // 1. range-check gate
        meta.create_gate("range check", |meta| {
            let q = meta.query_selector(q_range_check);

            // note that we don't need to specify the rotation when querying the `selctor`
            // That's because the selector always get queried at the current row .
            // While the `advice columns` get queried relatively to the selector offset, so we need to specify the relative rotation
            // 然而 advice col 是相对于选择器偏移量(Selector offset)进行查询的，所以我们需要指定 relative rotation.
            let value = meta.query_advice(value, Rotation::cur());

            // Given a range R and a value v, returns the multiplication expression
            //  (v) * (1 - v) * (2 - v) * ... * (R - 1 - v)
            let range_check = |range: usize, value: Expression<F>| {
                assert!(range > 0);
                (1..range).fold(value.clone(), |expr, i| {
                    expr * (Expression::Constant(F::from(i as u64)) - value.clone())
                })
            };
            // like the previously using "vec![s * (a + b - c)]",
            // multiplies the specified constraint by the selector, api 将指定的约束 × Selector
            Constraints::with_selector(q, [("range check", range_check(RANGE, value))])
        });
        
        // 2. Lookup Gate  - range-check using lookup argument
        // 这个查找表将会在后面的范围检查中使用，以便在某些情况下使用查找表, 而不是表达式来执行范围检查。
        meta.lookup(|meta| {
            let q_lookup = meta.query_selector(q_lookup);
            let value = meta.query_advice(value, Rotation::cur());

            vec![(q_lookup * value, table.value)]
        });

        config
    }

    // pass `value` and assign it on the offset.
    pub fn assign_simple(
        &self,
        mut layouter: impl Layouter<F>,
        value: Value<Assigned<F>>,
    ) -> Result<RangeConstrained<F, RANGE>, Error> {
        layouter.assign_region(
            || "Assign value for simple range check",
            |mut region| {
                let offset = 0;

                // Enable q_range_check Selector.
                self.q_range_check.enable(&mut region, offset)?;

                // Assign `value` 
                region
                    .assign_advice(
                        || "value", 
                        self.value,  // current col ?
                        offset, 
                        || value
                    ).map(RangeConstrained) // 将结果转化为 RangeConstrained 类型
            },
        )
    }

    pub fn assign_lookup(
        &self,
        mut layouter: impl Layouter<F>,
        value: Value<Assigned<F>>,
    ) -> Result<RangeConstrained<F, LOOKUP_RANGE>, Error> {
        layouter.assign_region(
            || "Assign value for lookup range check",
            |mut region| {
                let offset = 0;

                // Enable q_lookup, 告诉约束系统在该区域应用这个选择器
                self.q_lookup.enable(&mut region, offset)?;

                // Assign value
                region
                    .assign_advice(|| "value", self.value, offset, || value)
                    .map(RangeConstrained)
                // assign_advice() 将 advice col 与值 value 关联，
                // 并将结果封装在 RangeConstrained struct 中
            },
        )
    }
}

// [cfg(test)]是一个条件编译属性，意思是只有在执行 test 时，此模块代码才会被编译和执行
// 好处是，当你在普通的编译或生产环境下构建你的程序时，测试代码不会被包括进去，
// 从而减少了编译时间和生成的可执行文件的大小。
#[cfg(test)]
mod tests {
    use halo2_proofs::{
        circuit::floor_planner::V1,
        dev::{FailureLocation, MockProver, VerifyFailure},
        pasta::Fp,
        plonk::{Any, Circuit},
    };

    use super::*;

    #[derive(Default)]
    struct MyCircuit<F: PrimeField, const RANGE: usize, const LOOKUP_RANGE: usize> {
        simple_value: Value<Assigned<F>>,
        lookup_value: Value<Assigned<F>>,
    }

    impl<F: PrimeField, const RANGE: usize, const LOOKUP_RANGE: usize> Circuit<F>
        for MyCircuit<F, RANGE, LOOKUP_RANGE>
    {
        type Config = RangeCheckConfig<F, RANGE, LOOKUP_RANGE>;
        type FloorPlanner = V1;

        fn without_witnesses(&self) -> Self { Self::default() }

        fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
            let value = meta.advice_column();
            RangeCheckConfig::configure(meta, value)
        }

        fn synthesize(
            &self,
            config: Self::Config,
            mut layouter: impl Layouter<F>,
        ) -> Result<(), Error> {
            // load lookup table.
            config.table.load(&mut layouter)?;

            config.assign_simple(
                layouter.namespace(|| "Assign simple(smaller) value"), 
                self.simple_value
            )?;
            config.assign_lookup(
                layouter.namespace(|| "Assign lookup(larger) value"),
                self.lookup_value,
            )?;
            Ok(())
        }
    }

    #[test]
    fn test_range_check_2() {
        // in every circuit, we opt to reserve the last few rows of each advice cols 
        // for random values which are blinding factors(for zk), so `k` is always larger.
        let k = 9;
        const RANGE: usize = 8; // 3-bit value
        const LOOKUP_RANGE: usize = 256; // 2^8, 8-bit value

        // Successful cases
        for i in 0..RANGE {
            for j in 0..LOOKUP_RANGE {
                // According to the <i, j> to construct different Circuit.
                //MyCircuit::<Fp,.. ,..> : 指定 Constant 泛型的值.
                let circuit = MyCircuit::<Fp, RANGE, LOOKUP_RANGE> {
                    simple_value: Value::known(Fp::from(i as u64).into()),
                    lookup_value: Value::known(Fp::from(j as u64).into()),
                };

                let prover = MockProver::run(k, &circuit, vec![]).unwrap();
                prover.assert_satisfied();
            }
        }

        // Out-of-range `value = 8`, `lookup_value = 256`
        {
            let circuit = MyCircuit::<Fp, RANGE, LOOKUP_RANGE> {
                simple_value: Value::known(Fp::from(RANGE as u64).into()),
                lookup_value: Value::known(Fp::from(LOOKUP_RANGE as u64).into()),
            };
            let prover = MockProver::run(k, &circuit, vec![]).unwrap();
            assert_eq!(
                prover.verify(),
                Err(vec![
                    VerifyFailure::ConstraintNotSatisfied {
                        constraint: ((0, "range check").into(), 0, "range check").into(),
                        location: FailureLocation::InRegion {
                            region: (1, "Assign value for simple range check").into(),
                            offset: 0
                        },
                        cell_values: vec![(((Any::Advice, 0).into(), 0).into(), "0x8".to_string())]
                    },
                    VerifyFailure::Lookup {
                        lookup_index: 0,
                        location: FailureLocation::InRegion {
                            region: (2, "Assign value for lookup range check").into(),
                            offset: 0
                        }
                    }
                ])
            );
        }
    }

    // $ cargo test --release --all-features print_range_check_2
    #[cfg(feature = "dev-graph")]
    #[test]
    fn print_range_check_2() {
        use plotters::prelude::*;

        let root = BitMapBackend::new("range-check-2-layout.png", (1024, 3096)).into_drawing_area();
        root.fill(&WHITE).unwrap();
        let root = root
            .titled("Range Check 2 Layout", ("sans-serif", 60))
            .unwrap();

        let circuit = MyCircuit::<Fp, 8, 256> {
            simple_value: Value::unknown(),
            lookup_value: Value::unknown(),
        };
        halo2_proofs::dev::CircuitLayout::default()
            .render(9, &circuit, &root)
            .unwrap();
    }
}
