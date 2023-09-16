use std::marker::PhantomData;

use ff::{Field, PrimeField};
use halo2_proofs::{
    circuit::{Layouter, Value},
    plonk::{ConstraintSystem, Error, TableColumn},
};

struct Sizes {
    RANGE: usize,
    NUM_BITS: usize,
    LOOKUP_RANGE: usize,
}

/// A lookup table of values from 0..RANGE.
#[derive(Debug, Clone)]
pub(super) struct RangeTableConfig<F: PrimeField, const RANGE: usize> {
    pub(super) value: TableColumn,
    pub(super) num_bits: TableColumn,
    _marker: PhantomData<F>,
}

impl<F: PrimeField, const RANGE: usize> RangeTableConfig<F, RANGE> {
    pub(super) fn configure(meta: &mut ConstraintSystem<F>) -> Self {
        let value = meta.lookup_table_column();
        let num_bits = meta.lookup_table_column();

        Self {
            value,
            num_bits,
            _marker: PhantomData,
        }
    }

    pub(super) fn load(&self, layouter: &mut impl Layouter<F>) -> Result<(), Error> {
        layouter.assign_table(
            || "load range-check table",
            |mut table| {
                // Assign the values
                let mut offset = 0;
                for value in 0..RANGE {
                    table.assign_cell(
                        || "value",
                        self.value,
                        offset,
                        || Value::known(F::from_u128(value as u128)),
                    )?;
                    offset += 1;
                }

                // Assign the number of bits per value
                let mut bitCount = 0;
                let mut currPow2 = 1;
                let mut currentBits = 0;
                offset = 0;
                for value in 0..RANGE {
                    table.assign_cell(
                        || "num_bits",
                        self.num_bits,
                        offset,
                        || Value::known(F::from(currentBits as u64)),
                    )?;
                    offset += 1;
                    bitCount += 1;
                    if bitCount >= currPow2 {
                        bitCount = 0;
                        currentBits += 1;
                        currPow2 *= 2;
                    }
                }

                Ok(())
            },
        )
    }
}