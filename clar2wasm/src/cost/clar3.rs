use std::collections::HashMap;

use clarity::vm::ClarityName;
use lazy_static::lazy_static;

use super::{Caf, WordCost};
use crate::words::arithmetic::{Add, Div, Log2, Modulo, Mul, Power, Sqrti, Sub};
use crate::words::bindings::Let;
use crate::words::bitwise::{
    BitwiseAnd, BitwiseLShift, BitwiseNot, BitwiseOr, BitwiseRShift, BitwiseXor,
};
use crate::words::blockinfo::{
    AtBlock, GetBlockInfo, GetBurnBlockInfo, GetStacksBlockInfo, GetTenureInfo,
};
use crate::words::buff_to_integer::{BuffToIntBe, BuffToIntLe, BuffToUintBe, BuffToUintLe};
use crate::words::comparison::{CmpGeq, CmpGreater, CmpLeq, CmpLess};
use crate::words::conditionals::{And, Asserts, Filter, If, Match, Or, Try, Unwrap, UnwrapErr};
use crate::words::consensus_buff::{FromConsensusBuff, ToConsensusBuff};
use crate::words::contract::{AsContract, ContractCall};
use crate::words::control_flow::{Begin, UnwrapErrPanic, UnwrapPanic};
use crate::words::conversion::{IntToAscii, IntToUtf8, StringToInt, StringToUint};
use crate::words::data_vars::{GetDataVar, SetDataVar};
use crate::words::default_to::DefaultTo;
use crate::words::enums::{ClarityErr, ClarityOk, ClaritySome};
use crate::words::equal::{IndexOf, IsEq};
use crate::words::hashing::{Hash160, Keccak256, Sha256, Sha512, Sha512_256};
use crate::words::logical::Not;
use crate::words::maps::{MapDelete, MapGet, MapInsert, MapSet};
use crate::words::noop::{ContractOf, ToInt, ToUint};
use crate::words::options::{IsNone, IsSome};
use crate::words::principal::{Construct, Destruct, IsStandard, PrincipalOf};
use crate::words::print::Print;
use crate::words::responses::{IsErr, IsOk};
use crate::words::secp256k1::{Recover, Verify};
use crate::words::sequences::{
    Append, AsMaxLen, Concat, ElementAt, Fold, Len, ListCons, Map, ReplaceAt, Slice,
};
use crate::words::stx::{StxBurn, StxGetAccount, StxGetBalance, StxTransfer, StxTransferMemo};
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
                runtime: Linear { a: 11, b: 125 },
                read_count: None,
                read_length: None,
                write_count: None,
                write_length: None,
            },
        );
        map.insert(
            Sub.name(),
            WordCost {
                runtime: Linear { a: 11, b: 125 },
                read_count: None,
                read_length: None,
                write_count: None,
                write_length: None,
            },
        );
        map.insert(
            Mul.name(),
            WordCost {
                runtime: Linear { a: 13, b: 125 },
                read_count: None,
                read_length: None,
                write_count: None,
                write_length: None,
            },
        );
        map.insert(
            Div.name(),
            WordCost {
                runtime: Linear { a: 13, b: 125 },
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
                runtime: Constant(133),
                read_count: None,
                read_length: None,
                write_count: None,
                write_length: None,
            },
        );
        map.insert(
            Modulo.name(),
            WordCost {
                runtime: Constant(141),
                read_count: None,
                read_length: None,
                write_count: None,
                write_length: None,
            },
        );
        map.insert(
            Power.name(),
            WordCost {
                runtime: Constant(143),
                read_count: None,
                read_length: None,
                write_count: None,
                write_length: None,
            },
        );
        map.insert(
            Sqrti.name(),
            WordCost {
                runtime: Constant(142),
                read_count: None,
                read_length: None,
                write_count: None,
                write_length: None,
            },
        );
        map.insert(
            BitwiseAnd.name(),
            WordCost {
                runtime: Linear { a: 15, b: 129 },
                read_count: None,
                read_length: None,
                write_count: None,
                write_length: None,
            },
        );
        map.insert(
            BitwiseOr.name(),
            WordCost {
                runtime: Linear { a: 15, b: 129 },
                read_count: None,
                read_length: None,
                write_count: None,
                write_length: None,
            },
        );
        map.insert(
            BitwiseXor.name(),
            WordCost {
                runtime: Linear { a: 15, b: 129 },
                read_count: None,
                read_length: None,
                write_count: None,
                write_length: None,
            },
        );
        map.insert(
            BitwiseNot.name(),
            WordCost {
                runtime: Constant(147),
                read_count: None,
                read_length: None,
                write_count: None,
                write_length: None,
            },
        );
        map.insert(
            BitwiseLShift.name(),
            WordCost {
                runtime: Constant(167),
                read_count: None,
                read_length: None,
                write_count: None,
                write_length: None,
            },
        );
        map.insert(
            BitwiseRShift.name(),
            WordCost {
                runtime: Constant(167),
                read_count: None,
                read_length: None,
                write_count: None,
                write_length: None,
            },
        );
        map.insert(
            BuffToIntLe.name(),
            WordCost {
                runtime: Constant(141),
                read_count: None,
                read_length: None,
                write_count: None,
                write_length: None,
            },
        );
        map.insert(
            BuffToIntBe.name(),
            WordCost {
                runtime: Constant(141),
                read_count: None,
                read_length: None,
                write_count: None,
                write_length: None,
            },
        );
        map.insert(
            BuffToUintLe.name(),
            WordCost {
                runtime: Constant(141),
                read_count: None,
                read_length: None,
                write_count: None,
                write_length: None,
            },
        );
        map.insert(
            BuffToUintBe.name(),
            WordCost {
                runtime: Constant(141),
                read_count: None,
                read_length: None,
                write_count: None,
                write_length: None,
            },
        );
        map.insert(
            CmpGreater.name(),
            WordCost {
                runtime: Linear { a: 7, b: 128 },
                read_count: None,
                read_length: None,
                write_count: None,
                write_length: None,
            },
        );
        map.insert(
            CmpGeq.name(),
            WordCost {
                runtime: Linear { a: 7, b: 128 },
                read_count: None,
                read_length: None,
                write_count: None,
                write_length: None,
            },
        );
        map.insert(
            CmpLess.name(),
            WordCost {
                runtime: Linear { a: 7, b: 128 },
                read_count: None,
                read_length: None,
                write_count: None,
                write_length: None,
            },
        );
        map.insert(
            CmpLeq.name(),
            WordCost {
                runtime: Linear { a: 7, b: 128 },
                read_count: None,
                read_length: None,
                write_count: None,
                write_length: None,
            },
        );
        map.insert(
            Or.name(),
            WordCost {
                runtime: Linear { a: 3, b: 120 },
                read_count: None,
                read_length: None,
                write_count: None,
                write_length: None,
            },
        );
        map.insert(
            And.name(),
            WordCost {
                runtime: Linear { a: 3, b: 120 },
                read_count: None,
                read_length: None,
                write_count: None,
                write_length: None,
            },
        );
        map.insert(
            Not.name(),
            WordCost {
                runtime: Constant(138),
                read_count: None,
                read_length: None,
                write_count: None,
                write_length: None,
            },
        );
        map.insert(
            IntToAscii.name(),
            WordCost {
                runtime: Constant(147),
                read_count: None,
                read_length: None,
                write_count: None,
                write_length: None,
            },
        );
        map.insert(
            IntToUtf8.name(),
            WordCost {
                runtime: Constant(181),
                read_count: None,
                read_length: None,
                write_count: None,
                write_length: None,
            },
        );
        map.insert(
            StringToInt.name(),
            WordCost {
                runtime: Constant(168),
                read_count: None,
                read_length: None,
                write_count: None,
                write_length: None,
            },
        );
        map.insert(
            StringToUint.name(),
            WordCost {
                runtime: Constant(168),
                read_count: None,
                read_length: None,
                write_count: None,
                write_length: None,
            },
        );
        map.insert(
            ToInt.name(),
            WordCost {
                runtime: Constant(135),
                read_count: None,
                read_length: None,
                write_count: None,
                write_length: None,
            },
        );
        map.insert(
            ToUint.name(),
            WordCost {
                runtime: Constant(135),
                read_count: None,
                read_length: None,
                write_count: None,
                write_length: None,
            },
        );
        map.insert(
            Hash160.name(),
            WordCost {
                runtime: Linear {  a: 1, b: 188 },
                read_count: None,
                read_length: None,
                write_count: None,
                write_length: None,
            },
        );
        map.insert(
            Keccak256.name(),
            WordCost {
                runtime: Linear {  a: 1, b: 127 },
                read_count: None,
                read_length: None,
                write_count: None,
                write_length: None,
            },
        );
        map.insert(
            Sha256.name(),
            WordCost {
                runtime: Linear {  a: 1, b: 100 },
                read_count: None,
                read_length: None,
                write_count: None,
                write_length: None,
            },
        );
        map.insert(
            Sha512.name(),
            WordCost {
                runtime: Linear {  a: 1, b: 176 },
                read_count: None,
                read_length: None,
                write_count: None,
                write_length: None,
            },
        );
        map.insert(
            Sha512_256.name(),
            WordCost {
                runtime: Linear {  a: 1, b: 56 },
                read_count: None,
                read_length: None,
                write_count: None,
                write_length: None,
            },
        );
        map.insert(
            Construct.name(),
            WordCost {
                runtime: Constant(398),
                read_count: None,
                read_length: None,
                write_count: None,
                write_length: None,
            },
        );
        map.insert(
            Destruct.name(),
            WordCost {
                runtime: Constant(314),
                read_count: None,
                read_length: None,
                write_count: None,
                write_length: None,
            },
        );
        map.insert(
            IsStandard.name(),
            WordCost {
                runtime: Constant(127),
                read_count: None,
                read_length: None,
                write_count: None,
                write_length: None,
            },
        );
        // TODO: check if this indeed costs nothing (SUSPICIOUS)
        map.insert(
            StxBurn.name(),
            WordCost {
                runtime: Constant(549),
                read_count: Constant(2),
                read_length: Constant(1),
                write_count: Constant(2),
                write_length: Constant(1),
            },
        );
        map.insert(
            StxGetAccount.name(),
            WordCost {
                runtime: Constant(4654),
                read_count: Constant(1),
                read_length: Constant(1),
                write_count: None,
                write_length: None,
            },
        );
        map.insert(
            StxGetBalance.name(),
            WordCost {
                runtime: Constant(4294),
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
                runtime: Linear { a: 117, b: 178 },
                read_count: None,
                read_length: None,
                write_count: None,
                write_length: None,
            }
        );
        map.insert(
            AtBlock.name(),
            WordCost {
                runtime: Constant(1327),
                read_count: Constant(1),
                read_length: Constant(1),
                write_count: None,
                write_length: None,
            },
        );
        map.insert(
            GetBlockInfo.name(),
            WordCost {
                runtime: Constant(6321),
                read_count: Constant(1),
                read_length: Constant(1),
                write_count: None,
                write_length: None,
            },
        );
        map.insert(
            GetBurnBlockInfo.name(),
            WordCost {
                runtime: Constant(96479),
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
                runtime: Constant(6321),
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
                runtime: Constant(128),
                read_count: None,
                read_length: None,
                write_count: None,
                write_length: None,
            },
        );
        map.insert(
            Filter.name(),
            WordCost {
                runtime: Constant(407),
                read_count: None,
                read_length: None,
                write_count: None,
                write_length: None,
            },
        );
        map.insert(
            If.name(),
            WordCost {
                runtime: Constant(168),
                read_count: None,
                read_length: None,
                write_count: None,
                write_length: None,
            },
        );
        map.insert(
            Match.name(),
            WordCost {
                runtime: Constant(264),
                read_count: None,
                read_length: None,
                write_count: None,
                write_length: None,
            },
        );
        map.insert(
            Try.name(),
            WordCost {
                runtime: Constant(240),
                read_count: None,
                read_length: None,
                write_count: None,
                write_length: None,
            },
        );
        map.insert(
            Unwrap.name(),
            WordCost {
                runtime: Constant(252),
                read_count: None,
                read_length: None,
                write_count: None,
                write_length: None,
            },
        );
        map.insert(
            UnwrapErr.name(),
            WordCost {
                runtime: Constant(248),
                read_count: None,
                read_length: None,
                write_count: None,
                write_length: None,
            },
        );
        map.insert(
            UnwrapErrPanic.name(),
            WordCost {
                runtime: Constant(302),
                read_count: None,
                read_length: None,
                write_count: None,
                write_length: None,
            },
        );
        map.insert(
            UnwrapPanic.name(),
            WordCost {
                runtime: Constant(274),
                read_count: None,
                read_length: None,
                write_count: None,
                write_length: None,
            },
        );
        map.insert(
            FromConsensusBuff.name(),
            WordCost {
                runtime: NLogN { a: 3, b: 185 },
                read_count: None,
                read_length: None,
                write_count: None,
                write_length: None,
            },
        );
        map.insert(
            ToConsensusBuff.name(),
            WordCost {
                runtime: Linear { a: 1, b: 233 },
                read_count: None,
                read_length: None,
                write_count: None,
                write_length: None,
            },
        );
        map.insert(
            AsContract.name(),
            WordCost {
                runtime: Constant(138),
                read_count: None,
                read_length: None,
                write_count: None,
                write_length: None,
            },
        );
        map.insert(
            ContractCall.name(),
            WordCost {
                runtime: Constant(134),
                read_count: None,
                read_length: None,
                write_count: None,
                write_length: None,
            },
        );
        map.insert(
            Begin.name(),
            WordCost {
                runtime: Constant(151),
                read_count: None,
                read_length: None,
                write_count: None,
                write_length: None,
            },
        );
        map.insert(
            GetDataVar.name(),
            WordCost {
                runtime: Linear { a: 1, b: 151 },
                read_count: Constant(1),
                read_length: Linear { a: 1, b: 1 },
                write_count: None,
                write_length: None,
            },
        );
        map.insert(
            SetDataVar.name(),
            WordCost {
                runtime: Linear { a: 5, b: 655 },
                read_count: None,
                read_length: None,
                write_count: Constant(1),
                write_length: Linear { a: 1, b: 1 },
            },
        );
        map.insert(
            DefaultTo.name(),
            WordCost {
                runtime: Constant(268),
                read_count: None,
                read_length: None,
                write_count: None,
                write_length: None,
            },
        );
        map.insert(
            ClarityOk.name(),
            WordCost {
                runtime: Constant(199),
                read_count: None,
                read_length: None,
                write_count: None,
                write_length: None,
            },
        );
        map.insert(
            ClarityErr.name(),
            WordCost {
                runtime: Constant(199),
                read_count: None,
                read_length: None,
                write_count: None,
                write_length: None,
            },
        );
        map.insert(
            ClaritySome.name(),
            WordCost {
                runtime: Constant(199),
                read_count: None,
                read_length: None,
                write_count: None,
                write_length: None,
            },
        );
        map.insert(
            IndexOf::Alias.name(),
            WordCost {
                runtime: Linear { a: 1, b: 211 },
                read_count: None,
                read_length: None,
                write_count: None,
                write_length: None,
            },
        );
        map.insert(
            IndexOf::Original.name(),
            WordCost {
                runtime: Linear { a: 1, b: 211 },
                read_count: None,
                read_length: None,
                write_count: None,
                write_length: None,
            },
        );
        map.insert(
            IsEq.name(),
            WordCost {
                runtime: Linear { a: 1, b: 151 },
                read_count: None,
                read_length: None,
                write_count: None,
                write_length: None,
            },
        );
        map.insert(
            MapGet.name(),
            WordCost {
                runtime: Linear { a: 1, b: 1025 },
                read_count: Constant(1),
                read_length: Linear { a: 1, b: 1},
                write_count: None,
                write_length: None,
            },
        );
        map.insert(
            MapSet.name(),
            WordCost {
                runtime: Linear { a: 4, b: 1899 },
                read_count: Constant(1),
                read_length: None,
                write_count: Constant(1),
                write_length: Linear { a: 1, b: 1},
            },
        );
        // TODO: check if this indeed costs the same as `map-set`
        map.insert(
            MapInsert.name(),
            WordCost {
                runtime: Linear { a: 4, b: 1899 },
                read_count: Constant(1),
                read_length: None,
                write_count: Constant(1),
                write_length: Linear { a: 1, b: 1},
            },
        );
        // TODO: check if this indeed costs the same as `map-set`
        map.insert(
            MapDelete.name(),
            WordCost {
                runtime: Linear { a: 4, b: 1899 },
                read_count: Constant(1),
                read_length: None,
                write_count: Constant(1),
                write_length: Linear { a: 1, b: 1},
            },
        );
        map.insert(
            ContractOf.name(),
            WordCost {
                runtime: Constant(13400),
                read_count: None,
                read_length: None,
                write_count: None,
                write_length: None,
            },
        );
        map.insert(
            IsNone.name(),
            WordCost {
                runtime: Constant(214),
                read_count: None,
                read_length: None,
                write_count: None,
                write_length: None,
            },
        );
        map.insert(
            IsSome.name(),
            WordCost {
                runtime: Constant(195),
                read_count: None,
                read_length: None,
                write_count: None,
                write_length: None,
            },
        );
        map.insert(
            PrincipalOf.name(),
            WordCost {
                runtime: Constant(984),
                read_count: None,
                read_length: None,
                write_count: None,
                write_length: None,
            },
        );
        map.insert(
            Print.name(),
            WordCost {
                runtime: Linear { a:15, b: 1458 },
                read_count: None,
                read_length: None,
                write_count: None,
                write_length: None,
            },
        );
        map.insert(
            IsOk.name(),
            WordCost {
                runtime: Constant(258),
                read_count: None,
                read_length: None,
                write_count: None,
                write_length: None,
            },
        );
        map.insert(
            IsErr.name(),
            WordCost {
                runtime: Constant(245),
                read_count: None,
                read_length: None,
                write_count: None,
                write_length: None,
            },
        );
        map.insert(
            Recover.name(),
            WordCost {
                runtime: Constant(8655),
                read_count: None,
                read_length: None,
                write_count: None,
                write_length: None,
            },
        );
        map.insert(
            Verify.name(),
            WordCost {
                runtime: Constant(8349),
                read_count: None,
                read_length: None,
                write_count: None,
                write_length: None,
            },
        );
        map.insert(
            Append.name(),
            WordCost {
                runtime: Linear { a: 73, b: 285 },
                read_count: None,
                read_length: None,
                write_count: None,
                write_length: None,
            },
        );
        map.insert(
            AsMaxLen.name(),
            WordCost {
                runtime: Constant(475),
                read_count: None,
                read_length: None,
                write_count: None,
                write_length: None,
            },
        );
        map.insert(
            Concat.name(),
            WordCost {
                runtime: Linear { a: 37, b: 220 },
                read_count: None,
                read_length: None,
                write_count: None,
                write_length: None,
            },
        );
        map.insert(
            ElementAt::Original.name(),
            WordCost {
                runtime: Constant(498),
                read_count: None,
                read_length: None,
                write_count: None,
                write_length: None,
            },
        );
        map.insert(
            ElementAt::Alias.name(),
            WordCost {
                runtime: Constant(498),
                read_count: None,
                read_length: None,
                write_count: None,
                write_length: None,
            },
        );
        map.insert(
            Fold.name(),
            WordCost {
                runtime: Constant(460),
                read_count: None,
                read_length: None,
                write_count: None,
                write_length: None,
            },
        );
        map.insert(
            Len.name(),
            WordCost {
                runtime: Constant(429),
                read_count: None,
                read_length: None,
                write_count: None,
                write_length: None,
            },
        );
        map.insert(
            ListCons.name(),
            WordCost {
                runtime: Linear { a: 14, b: 164 },
                read_count: None,
                read_length: None,
                write_count: None,
                write_length: None,
            },
        );
        map.insert(
            Map.name(),
            WordCost {
                runtime: Linear { a: 1198, b: 3067 },
                read_count: None,
                read_length: None,
                write_count: None,
                write_length: None,
            },
        );
        map.insert(
            ReplaceAt.name(),
            WordCost {
                runtime: Linear { a: 1, b: 561 },
                read_count: None,
                read_length: None,
                write_count: None,
                write_length: None,
            },
        );
        map.insert(
            Slice.name(),
            WordCost {
                runtime: Constant(498),
                read_count: None,
                read_length: None,
                write_count: None,
                write_length: None,
            },
        );
        map.insert(
            StxTransfer.name(),
            WordCost {
                runtime: Constant(4640),
                read_count: Constant(1),
                read_length: Constant(1),
                write_count: Constant(1),
                write_length: Constant(1),
            },
        );
        map.insert(
            StxTransferMemo.name(),
            WordCost {
                runtime: Constant(4709),
                read_count: Constant(1),
                read_length: Constant(1),
                write_count: Constant(1),
                write_length: Constant(1),
            },
        );
        map.insert(
            MintFungibleToken.name(),
            WordCost {
                runtime: Constant(1479),
                read_count: Constant(2),
                read_length: Constant(1),
                write_count: Constant(2),
                write_length: Constant(1),
            },
        );
        map.insert(
            BurnFungibleToken.name(),
            WordCost {
                runtime: Constant(549),
                read_count: Constant(2),
                read_length: Constant(1),
                write_count: Constant(2),
                write_length: Constant(1),
            },
        );
        map.insert(
            TransferFungibleToken.name(),
            WordCost {
                runtime: Constant(549),
                read_count: Constant(2),
                read_length: Constant(1),
                write_count: Constant(2),
                write_length: Constant(1),
            },
        );
        map.insert(
            GetSupplyOfFungibleToken.name(),
            WordCost {
                runtime: Constant(420),
                read_count: Constant(1),
                read_length: Constant(1),
                write_count: None,
                write_length: None,
            },
        );
        map.insert(
            GetBalanceOfFungibleToken.name(),
            WordCost {
                runtime: Constant(479),
                read_count: Constant(1),
                read_length: Constant(1),
                write_count: None,
                write_length: None,
            },
        );
        map.insert(
            MintNonFungibleToken.name(),
            WordCost {
                runtime: Linear { a: 9, b: 575 },
                read_count: Constant(1),
                read_length: Constant(1),
                write_count: Constant(1),
                write_length: Constant(1),
            },
        );
        map.insert(
            BurnNonFungibleToken.name(),
            WordCost {
                runtime: Linear { a: 9, b: 572 },
                read_count: Constant(1),
                read_length: Constant(1),
                write_count: Constant(1),
                write_length: Constant(1),
            },
        );
        map.insert(
            TransferNonFungibleToken.name(),
            WordCost {
                runtime: Linear { a: 9, b: 572 },
                read_count: Constant(1),
                read_length: Constant(1),
                write_count: Constant(1),
                write_length: Constant(1),
            },
        );
        map.insert(
            GetOwnerOfNonFungibleToken.name(),
            WordCost {
                runtime: Linear { a: 9, b: 795 },
                read_count: Constant(1),
                read_length: Constant(1),
                write_count: None,
                write_length: None,
            },
        );
        map.insert(
            TupleCons.name(),
            WordCost {
                runtime: NLogN { a: 10, b: 1876 },
                read_count: None,
                read_length: None,
                write_count: None,
                write_length: None,
            },
        );
        map.insert(
            TupleGet.name(),
            WordCost {
                runtime: NLogN { a: 4, b: 1736 },
                read_count: None,
                read_length: None,
                write_count: None,
                write_length: None,
            },
        );
        map.insert(
            TupleMerge.name(),
            WordCost {
                runtime: Linear { a: 4, b: 408 },
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
