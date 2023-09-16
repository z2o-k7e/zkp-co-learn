// here we are gonna define our lookup table
// A lookup table of values up to RANGE 
// e.g. RANGE = 256, values = [0..255]
// Once this is create it can be used inside our main config! 

use std::marker::PhantomData;
use ff::{Field, PrimeField};
use halo2_proofs::{
    circuit::{Layouter, Value},
    plonk::{ConstraintSystem, Error, TableColumn},
};

/// pub(super) 仅当前模块的父模块中可见，但不对外公开
/// A lookup table of values from 0..RANGE. 
/// TableColumn is a Fixed Column
#[derive(Debug, Clone)]
pub(super) struct RangeTableConfig<F: PrimeField, const RANGE: usize> {
    pub(super) value: TableColumn, 
    // 这个 struct 中存在一个与类型 F 相关的关联，即使 struct 自身并没有实际使用这个类型
    _marker: PhantomData<F>,
}

impl<F: PrimeField, const RANGE: usize> RangeTableConfig<F, RANGE> {
    pub(super) fn configure(meta: &mut ConstraintSystem<F>) -> Self {
        // API to create this special fixed colum
        let value = meta.lookup_table_column();

        Self {
            value,
            _marker: PhantomData,
        }
    }

    // load function assign the values to our fixed table
    // This action is performed at key gen time
    pub(super) fn load(&self, layouter: &mut impl Layouter<F>) -> Result<(), Error> {
        // firstly, for some RANGE we want to load all the values and assign it to the lookup table
        // assign_table is a special api that only works for lookup tables
        layouter.assign_table (
            || "load range-check table",
            |mut table| {
                // from row_0 to row_{RANGE-1}
                let mut offset = 0;
                for value in 0..RANGE {
                    table.assign_cell(
                        || "num_bits",
                        self.value,
                        offset,  // row num
                        || Value::known(F::from(value as u64)), // assigned value
                    )?;
                    offset += 1;  // 循环向下赋值, 直到填满 RANGE 所需的所有列
                }

                Ok(()) // return empty tuple (∵ Result<(), Error>)
            },
        )
    }
}
