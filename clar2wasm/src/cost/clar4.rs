use std::collections::HashMap;

use clarity::vm::ClarityName;
use lazy_static::lazy_static;

use super::{Caf, WordCost};
use crate::cost::clar3;
use crate::words::contract::{AsContractSafe, ContractHash, RestrictAssets};
use crate::words::to_ascii::ToAscii;
use crate::words::Word;

lazy_static! {
    pub(super) static ref WORD_COSTS: HashMap<ClarityName, WordCost> = {
        use Caf::*;

        let mut map = clar3::WORD_COSTS.clone();

        map.insert(
            ContractHash.name(),
            WordCost {
                runtime: Constant(180),
                read_count: Constant(1),
                read_length: Constant(32),
                write_count: None,
                write_length: None,
            },
        );

        map.insert(
            ToAscii.name(),
            WordCost {
                runtime: Linear { a: 16, b: 150 },
                read_count: None,
                read_length: None,
                write_count: None,
                write_length: None,
            },
        );

        map.insert(
            RestrictAssets.name(),
            WordCost {
                runtime: Linear { a: 125, b: 750 },
                read_count: None,
                read_length: None,
                write_count: None,
                write_length: None,
            },
        );

        map.insert(
            AsContractSafe.name(),
            WordCost {
                runtime: Linear { a: 125, b: 888 },
                read_count: None,
                read_length: None,
                write_count: None,
                write_length: None,
            },
        );

        map.insert(
            crate::words::secp256r1::Verify.name(),
            WordCost {
                runtime: Constant(51750),
                read_count: None,
                read_length: None,
                write_count: None,
                write_length: None,
            },
        );

        map
    };
}
