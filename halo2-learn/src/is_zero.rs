use ff::{Field, PrimeField};
use halo2_proofs::{circuit::*, plonk::*, poly::Rotation};

#[derive(Clone, Debug)]
pub struct IsZeroConfig<F> {
    pub value_inv: Column<Advice>,
    pub is_zero_expr: Expression<F>,
}

impl<F: PrimeField> IsZeroConfig<F> {
    pub fn expr(&self) -> Expression<F> {
        self.is_zero_expr.clone()
    }
}

pub struct IsZeroChip<F: PrimeField> {
    config: IsZeroConfig<F>,
}

impl<F: PrimeField> IsZeroChip<F> {
    pub fn construct(config: IsZeroConfig<F>) -> Self {
        IsZeroChip { config }
    }

    pub fn configure(
        meta: &mut ConstraintSystem<F>,
        q_enable: impl FnOnce(&mut VirtualCells<'_, F>) -> Expression<F>,
        value: impl FnOnce(&mut VirtualCells<'_, F>) -> Expression<F>,
        value_inv: Column<Advice>,
    ) -> IsZeroConfig<F> {
        let mut is_zero_expr = Expression::Constant(F::ZERO);

        meta.create_gate("is_zero", |meta| {
            //
            // valid | val |  val_inv |  1 - val * val_inv | val * (1 - val * val_inv)
            // ------+-----+----------+--------------------+-------------------
            //  yes  |  x  |    1/x   |        0           |   0
            //  no   |  x  |    0     |        1           |   x
            //  yes  |  0  |    0     |        1           |   0
            //  yes  |  0  |    y     |        1           |   0

            // value() is a fn takes the virtual cell. and return a Expression.
            let value = value(meta);   // passed in a Closure.
            let q_enable = q_enable(meta); // passed in a Closure.
            let value_inv = meta.query_advice(value_inv, Rotation::cur());

            // create a constant —— use Expression::Constant
            is_zero_expr = Expression::Constant(F::ONE) - value.clone() * value_inv;
            vec![q_enable * value * is_zero_expr.clone()]  // gate's constraints
        });

        IsZeroConfig {
            value_inv,
            is_zero_expr,
        }
    }

    pub fn assign(
        &self,
        region: &mut Region<'_, F>,
        offset: usize,
        value: Value<F>,
    ) -> Result<(), Error> {
        // value.invert()  OR  F::ZERO
        let value_inv = value.map(|value| value.invert().unwrap_or(F::ZERO));
        region.assign_advice(|| "value inv", 
          self.config.value_inv, 
          offset, 
          || value_inv
        )?;
        Ok(())
    }
}
