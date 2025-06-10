use std::collections::HashMap;

use clarity::vm::ClarityName;
use lazy_static::lazy_static;

use super::{Caf, WordCost};
use crate::words::arithmetic::{Add, Div, Log2, Modulo, Mul, Power, Sqrti, Sub};
use crate::words::bindings::Let;
use crate::words::blockinfo::{AtBlock, GetBlockInfo, GetStacksBlockInfo, GetTenureInfo};
use crate::words::comparison::{CmpGeq, CmpGreater, CmpLeq, CmpLess};
use crate::words::conditionals::{And, Asserts, Filter, If, Match, Or, Try, Unwrap, UnwrapErr};
use crate::words::contract::ContractCall;
use crate::words::control_flow::{Begin, UnwrapErrPanic, UnwrapPanic};
use crate::words::data_vars::{GetDataVar, SetDataVar};
use crate::words::default_to::DefaultTo;
use crate::words::enums::{ClarityErr, ClarityOk, ClaritySome};
use crate::words::equal::{IndexOf, IsEq};
use crate::words::hashing::{Hash160, Keccak256, Sha256, Sha512, Sha512_256};
use crate::words::logical::Not;
use crate::words::maps::{MapDelete, MapGet, MapInsert, MapSet};
use crate::words::noop::{ContractOf, ToInt, ToUint};
use crate::words::options::{IsNone, IsSome};
use crate::words::principal::PrincipalOf;
use crate::words::print::Print;
use crate::words::responses::{IsErr, IsOk};
use crate::words::secp256k1::{Recover, Verify};
use crate::words::sequences::{Append, AsMaxLen, Concat, ElementAt, Fold, Len, ListCons, Map};
use crate::words::stx::{StxBurn, StxGetBalance, StxTransfer};
use crate::words::tokens::{
    BurnFungibleToken, BurnNonFungibleToken, GetBalanceOfFungibleToken, GetOwnerOfNonFungibleToken,
    GetSupplyOfFungibleToken, MintFungibleToken, MintNonFungibleToken, TransferFungibleToken,
    TransferNonFungibleToken,
};
use crate::words::tuples::{TupleCons, TupleGet, TupleMerge};
use crate::words::Word;

lazy_static! {
    pub(super) static ref WORD_COSTS: HashMap<ClarityName, WordCost> = {
        use Caf::*;

        let mut map = HashMap::new();

        // simple variadic words

        map.insert(
            Add.name(),
            WordCost {
                runtime: Linear { a: 1000, b: 1000 },
                read_count: None,
                read_length: None,
                write_count: None,
                write_length: None,
            },
        );
        map.insert(
            Sub.name(),
            WordCost {
                runtime: Linear { a: 1000, b: 1000 },
                read_count: None,
                read_length: None,
                write_count: None,
                write_length: None,
            },
        );
        map.insert(
            Mul.name(),
            WordCost {
                runtime: Linear { a: 1000, b: 1000 },
                read_count: None,
                read_length: None,
                write_count: None,
                write_length: None,
            },
        );
        map.insert(
            Div.name(),
            WordCost {
                runtime: Linear { a: 1000, b: 1000 },
                read_count: None,
                read_length: None,
                write_count: None,
                write_length: None,
            },
        );

        // simple words

        map.insert(
            Log2.name(),
            WordCost {
                runtime: Constant(1000),
                read_count: None,
                read_length: None,
                write_count: None,
                write_length: None,
            },
        );
        map.insert(
            Modulo.name(),
            WordCost {
                runtime: Constant(1000),
                read_count: None,
                read_length: None,
                write_count: None,
                write_length: None,
            },
        );
        map.insert(
            Power.name(),
            WordCost {
                runtime: Constant(1000),
                read_count: None,
                read_length: None,
                write_count: None,
                write_length: None,
            },
        );
        map.insert(
            Sqrti.name(),
            WordCost {
                runtime: Constant(1000),
                read_count: None,
                read_length: None,
                write_count: None,
                write_length: None,
            },
        );
        map.insert(
            CmpGreater.name(),
            WordCost {
                runtime: Constant(1000),
                read_count: None,
                read_length: None,
                write_count: None,
                write_length: None,
            },
        );
        map.insert(
            CmpGeq.name(),
            WordCost {
                runtime: Constant(1000),
                read_count: None,
                read_length: None,
                write_count: None,
                write_length: None,
            },
        );
        map.insert(
            CmpLess.name(),
            WordCost {
                runtime: Constant(1000),
                read_count: None,
                read_length: None,
                write_count: None,
                write_length: None,
            },
        );
        map.insert(
            CmpLeq.name(),
            WordCost {
                runtime: Constant(1000),
                read_count: None,
                read_length: None,
                write_count: None,
                write_length: None,
            },
        );
        map.insert(
            Or.name(),
            WordCost {
                runtime: Linear { a: 1000, b: 1000 },
                read_count: None,
                read_length: None,
                write_count: None,
                write_length: None,
            },
        );
        map.insert(
            And.name(),
            WordCost {
                runtime: Linear { a: 1000, b: 1000 },
                read_count: None,
                read_length: None,
                write_count: None,
                write_length: None,
            },
        );
        map.insert(
            Not.name(),
            WordCost {
                runtime: Constant(1000),
                read_count: None,
                read_length: None,
                write_count: None,
                write_length: None,
            },
        );
        map.insert(
            ToInt.name(),
            WordCost {
                runtime: Constant(1000),
                read_count: None,
                read_length: None,
                write_count: None,
                write_length: None,
            },
        );
        map.insert(
            ToUint.name(),
            WordCost {
                runtime: Constant(1000),
                read_count: None,
                read_length: None,
                write_count: None,
                write_length: None,
            },
        );
        map.insert(
            Hash160.name(),
            WordCost {
                runtime: Linear { a: 1000, b: 1000 },
                read_count: None,
                read_length: None,
                write_count: None,
                write_length: None,
            },
        );
        map.insert(
            Keccak256.name(),
            WordCost {
                runtime: Linear { a: 1000, b: 1000 },
                read_count: None,
                read_length: None,
                write_count: None,
                write_length: None,
            },
        );
        map.insert(
            Sha256.name(),
            WordCost {
                runtime: Linear { a: 1000, b: 1000 },
                read_count: None,
                read_length: None,
                write_count: None,
                write_length: None,
            },
        );
        map.insert(
            Sha512.name(),
            WordCost {
                runtime: Linear { a: 1000, b: 1000 },
                read_count: None,
                read_length: None,
                write_count: None,
                write_length: None,
            },
        );
        map.insert(
            Sha512_256.name(),
            WordCost {
                runtime: Linear { a: 1000, b: 1000 },
                read_count: None,
                read_length: None,
                write_count: None,
                write_length: None,
            },
        );
        map.insert(
            StxBurn.name(),
            WordCost {
                runtime: Constant(1000),
                read_count: Constant(2),
                read_length: Constant(1),
                write_count: Constant(2),
                write_length: Constant(1),
            },
        );
        map.insert(
            StxGetBalance.name(),
            WordCost {
                runtime: Constant(1000),
                read_count: Constant(1),
                read_length: Constant(1),
                write_count: None,
                write_length: None,
            },
        );

        // complex words

        map.insert(
            Let.name(),
            WordCost {
                runtime: Linear { a: 1000, b: 1000 },
                read_count: None,
                read_length: None,
                write_count: None,
                write_length: None,
            }
        );
        map.insert(
            AtBlock.name(),
            WordCost {
                runtime: Constant(1000),
                read_count: Constant(1),
                read_length: Constant(1),
                write_count: None,
                write_length: None,
            },
        );
        map.insert(
            GetBlockInfo.name(),
            WordCost {
                runtime: Constant(1000),
                read_count: Constant(1),
                read_length: Constant(1),
                write_count: None,
                write_length: None,
            },
        );
        // TODO: check if this indeed costs the same as `get_block_info`
        map.insert(
            GetStacksBlockInfo.name(),
            WordCost {
                runtime: Constant(1000),
                read_count: Constant(1),
                read_length: Constant(1),
                write_count: None,
                write_length: None,
            },
        );
        // TODO: check if this indeed costs nothing (SUSPICIOUS)
        map.insert(
            GetTenureInfo.name(),
            WordCost {
                runtime: None,
                read_count: None,
                read_length: None,
                write_count: None,
                write_length: None,
            },
        );
        map.insert(
            Asserts.name(),
            WordCost {
                runtime: Constant(1000),
                read_count: None,
                read_length: None,
                write_count: None,
                write_length: None,
            },
        );
        map.insert(
            Filter.name(),
            WordCost {
                runtime: Constant(1000),
                read_count: None,
                read_length: None,
                write_count: None,
                write_length: None,
            },
        );
        map.insert(
            If.name(),
            WordCost {
                runtime: Constant(1000),
                read_count: None,
                read_length: None,
                write_count: None,
                write_length: None,
            },
        );
        map.insert(
            Match.name(),
            WordCost {
                runtime: Constant(1000),
                read_count: None,
                read_length: None,
                write_count: None,
                write_length: None,
            },
        );
        map.insert(
            Try.name(),
            WordCost {
                runtime: Constant(1000),
                read_count: None,
                read_length: None,
                write_count: None,
                write_length: None,
            },
        );
        map.insert(
            Unwrap.name(),
            WordCost {
                runtime: Constant(1000),
                read_count: None,
                read_length: None,
                write_count: None,
                write_length: None,
            },
        );
        map.insert(
            UnwrapErr.name(),
            WordCost {
                runtime: Constant(1000),
                read_count: None,
                read_length: None,
                write_count: None,
                write_length: None,
            },
        );
        map.insert(
            UnwrapErrPanic.name(),
            WordCost {
                runtime: Constant(1000),
                read_count: None,
                read_length: None,
                write_count: None,
                write_length: None,
            },
        );
        map.insert(
            UnwrapPanic.name(),
            WordCost {
                runtime: Constant(1000),
                read_count: None,
                read_length: None,
                write_count: None,
                write_length: None,
            },
        );
        map.insert(
            ContractCall.name(),
            WordCost {
                runtime: Constant(1000),
                read_count: None,
                read_length: None,
                write_count: None,
                write_length: None,
            },
        );
        map.insert(
            Begin.name(),
            WordCost {
                runtime: Constant(1000),
                read_count: None,
                read_length: None,
                write_count: None,
                write_length: None,
            },
        );
        map.insert(
            GetDataVar.name(),
            WordCost {
                runtime: Linear { a: 1000, b: 1000 },
                read_count: Constant(1),
                read_length: Linear { a: 1, b: 1 },
                write_count: None,
                write_length: None,
            },
        );
        map.insert(
            SetDataVar.name(),
            WordCost {
                runtime: Linear { a: 1000, b: 1000 },
                read_count: None,
                read_length: None,
                write_count: Constant(1),
                write_length: Linear { a: 1, b: 1 },
            },
        );
        map.insert(
            DefaultTo.name(),
            WordCost {
                runtime: Constant(1000),
                read_count: None,
                read_length: None,
                write_count: None,
                write_length: None,
            },
        );
        map.insert(
            ClarityOk.name(),
            WordCost {
                runtime: Constant(1000),
                read_count: None,
                read_length: None,
                write_count: None,
                write_length: None,
            },
        );
        map.insert(
            ClarityErr.name(),
            WordCost {
                runtime: Constant(1000),
                read_count: None,
                read_length: None,
                write_count: None,
                write_length: None,
            },
        );
        map.insert(
            ClaritySome.name(),
            WordCost {
                runtime: Constant(1000),
                read_count: None,
                read_length: None,
                write_count: None,
                write_length: None,
            },
        );
        map.insert(
            IndexOf::Alias.name(),
            WordCost {
                runtime: Linear { a: 1000, b: 1000 },
                read_count: None,
                read_length: None,
                write_count: None,
                write_length: None,
            },
        );
        map.insert(
            IndexOf::Original.name(),
            WordCost {
                runtime: Linear { a: 1000, b: 1000 },
                read_count: None,
                read_length: None,
                write_count: None,
                write_length: None,
            },
        );
        map.insert(
            IsEq.name(),
            WordCost {
                runtime: Linear { a: 1000, b: 1000 },
                read_count: None,
                read_length: None,
                write_count: None,
                write_length: None,
            },
        );
        map.insert(
            MapGet.name(),
            WordCost {
                runtime: Linear { a: 1000, b: 1000 },
                read_count: Constant(1),
                read_length: Linear { a: 1, b: 1 },
                write_count: None,
                write_length: None,
            },
        );
        map.insert(
            MapSet.name(),
            WordCost {
                runtime: Linear { a: 1000, b: 1000 },
                read_count: Constant(1),
                read_length: None,
                write_count: Constant(1),
                write_length: Linear { a: 1, b: 1 },
            },
        );
        // TODO: check if this indeed costs the same as `map-set`
        map.insert(
            MapInsert.name(),
            WordCost {
                runtime: Linear { a: 1000, b: 1000 },
                read_count: Constant(1),
                read_length: None,
                write_count: Constant(1),
                write_length: Linear { a: 1, b: 1 },
            },
        );
        // TODO: check if this indeed costs the same as `map-set`
        map.insert(
            MapDelete.name(),
            WordCost {
                runtime: Linear { a: 1000, b: 1000 },
                read_count: Constant(1),
                read_length: None,
                write_count: Constant(1),
                write_length: Linear { a: 1, b: 1 },
            },
        );
        map.insert(
            ContractOf.name(),
            WordCost {
                runtime: Constant(1000),
                read_count: None,
                read_length: None,
                write_count: None,
                write_length: None,
            },
        );
        map.insert(
            IsNone.name(),
            WordCost {
                runtime: Constant(1000),
                read_count: None,
                read_length: None,
                write_count: None,
                write_length: None,
            },
        );
        map.insert(
            IsSome.name(),
            WordCost {
                runtime: Constant(1000),
                read_count: None,
                read_length: None,
                write_count: None,
                write_length: None,
            },
        );
        map.insert(
            PrincipalOf.name(),
            WordCost {
                runtime: Constant(1000),
                read_count: None,
                read_length: None,
                write_count: None,
                write_length: None,
            },
        );
        map.insert(
            Print.name(),
            WordCost {
                runtime: Linear { a:1000, b: 1000 },
                read_count: None,
                read_length: None,
                write_count: None,
                write_length: None,
            },
        );
        map.insert(
            IsOk.name(),
            WordCost {
                runtime: Constant(1000),
                read_count: None,
                read_length: None,
                write_count: None,
                write_length: None,
            },
        );
        map.insert(
            IsErr.name(),
            WordCost {
                runtime: Constant(1000),
                read_count: None,
                read_length: None,
                write_count: None,
                write_length: None,
            },
        );
        map.insert(
            Recover.name(),
            WordCost {
                runtime: Constant(1000),
                read_count: None,
                read_length: None,
                write_count: None,
                write_length: None,
            },
        );
        map.insert(
            Verify.name(),
            WordCost {
                runtime: Constant(1000),
                read_count: None,
                read_length: None,
                write_count: None,
                write_length: None,
            },
        );
        map.insert(
            Append.name(),
            WordCost {
                runtime: Linear { a: 1000, b: 1000 },
                read_count: None,
                read_length: None,
                write_count: None,
                write_length: None,
            },
        );
        map.insert(
            AsMaxLen.name(),
            WordCost {
                runtime: Constant(1000),
                read_count: None,
                read_length: None,
                write_count: None,
                write_length: None,
            },
        );
        map.insert(
            Concat.name(),
            WordCost {
                runtime: Linear { a: 1000, b: 1000 },
                read_count: None,
                read_length: None,
                write_count: None,
                write_length: None,
            },
        );
        map.insert(
            ElementAt::Original.name(),
            WordCost {
                runtime: Constant(1000),
                read_count: None,
                read_length: None,
                write_count: None,
                write_length: None,
            },
        );
        map.insert(
            ElementAt::Alias.name(),
            WordCost {
                runtime: Constant(1000),
                read_count: None,
                read_length: None,
                write_count: None,
                write_length: None,
            },
        );
        map.insert(
            Fold.name(),
            WordCost {
                runtime: Constant(1000),
                read_count: None,
                read_length: None,
                write_count: None,
                write_length: None,
            },
        );
        map.insert(
            Len.name(),
            WordCost {
                runtime: Constant(1000),
                read_count: None,
                read_length: None,
                write_count: None,
                write_length: None,
            },
        );
        map.insert(
            ListCons.name(),
            WordCost {
                runtime: Linear { a: 1000, b: 1000 },
                read_count: None,
                read_length: None,
                write_count: None,
                write_length: None,
            },
        );
        map.insert(
            Map.name(),
            WordCost {
                runtime: Linear { a: 1000, b: 1000 },
                read_count: None,
                read_length: None,
                write_count: None,
                write_length: None,
            },
        );
        map.insert(
            StxTransfer.name(),
            WordCost {
                runtime: Constant(1000),
                read_count: Constant(1),
                read_length: Constant(1),
                write_count: Constant(1),
                write_length: Constant(1),
            },
        );
        map.insert(
            MintFungibleToken.name(),
            WordCost {
                runtime: Constant(1000),
                read_count: Constant(2),
                read_length: Constant(1),
                write_count: Constant(2),
                write_length: Constant(1),
            },
        );
        map.insert(
            BurnFungibleToken.name(),
            WordCost {
                runtime: Constant(1000),
                read_count: Constant(2),
                read_length: Constant(1),
                write_count: Constant(2),
                write_length: Constant(1),
            },
        );
        map.insert(
            TransferFungibleToken.name(),
            WordCost {
                runtime: Constant(1000),
                read_count: Constant(2),
                read_length: Constant(1),
                write_count: Constant(2),
                write_length: Constant(1),
            },
        );
        map.insert(
            GetSupplyOfFungibleToken.name(),
            WordCost {
                runtime: Constant(1000),
                read_count: Constant(1),
                read_length: Constant(1),
                write_count: None,
                write_length: None,
            },
        );
        map.insert(
            GetBalanceOfFungibleToken.name(),
            WordCost {
                runtime: Constant(1000),
                read_count: Constant(1),
                read_length: Constant(1),
                write_count: None,
                write_length: None,
            },
        );
        map.insert(
            MintNonFungibleToken.name(),
            WordCost {
                runtime: Linear { a: 1000, b: 1000 },
                read_count: Constant(1),
                read_length: Constant(1),
                write_count: Constant(1),
                write_length: Constant(1),
            },
        );
        map.insert(
            BurnNonFungibleToken.name(),
            WordCost {
                runtime: Linear { a: 1000, b: 1000 },
                read_count: Constant(1),
                read_length: Constant(1),
                write_count: Constant(1),
                write_length: Constant(1),
            },
        );
        map.insert(
            TransferNonFungibleToken.name(),
            WordCost {
                runtime: Linear { a: 1000, b: 1000 },
                read_count: Constant(1),
                read_length: Constant(1),
                write_count: Constant(1),
                write_length: Constant(1),
            },
        );
        map.insert(
            GetOwnerOfNonFungibleToken.name(),
            WordCost {
                runtime: Linear { a: 1000, b: 1000 },
                read_count: Constant(1),
                read_length: Constant(1),
                write_count: None,
                write_length: None,
            },
        );
        map.insert(
            TupleCons.name(),
            WordCost {
                runtime: NLogN { a: 1000, b: 1000 },
                read_count: None,
                read_length: None,
                write_count: None,
                write_length: None,
            },
        );
        map.insert(
            TupleGet.name(),
            WordCost {
                runtime: LogN { a: 1000, b: 1000 },
                read_count: None,
                read_length: None,
                write_count: None,
                write_length: None,
            },
        );
        map.insert(
            TupleMerge.name(),
            WordCost {
                runtime: Linear { a: 1000, b: 1000 },
                read_count: None,
                read_length: None,
                write_count: None,
                write_length: None,
            },
        );

        // TODO: check if these are indeed only relevant during analysis
        //
        // DefineConstant
        // DefineDataVar
        // DefinePrivateFunction
        // DefinePublicFunction
        // DefineReadOnlyFunction
        // DefineFungibleToken
        // DefineNonFungibleToken
        // DefineTrait

        map
    };
}
