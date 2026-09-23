use std::collections::HashMap;

use clarity::vm::ClarityName;
use lazy_static::lazy_static;

use super::{Caf, WordCost};
use crate::cost::clar4;
use crate::words::arithmetic::{Add, Div, Log2, Modulo, Mul, Power, Sqrti, Sub};
use crate::words::bindings::Let;
use crate::words::bitcoin::{GetTxOutput, VerifyMerkleProof};
use crate::words::bitwise::{
    BitwiseAnd, BitwiseLShift, BitwiseNot, BitwiseOr, BitwiseRShift, BitwiseXor,
};
use crate::words::buff_to_integer::{BuffToIntBe, BuffToIntLe, BuffToUintBe, BuffToUintLe};
use crate::words::comparison::{CmpGeq, CmpGreater, CmpLeq, CmpLess};
use crate::words::conditionals::{And, Filter, Match, Or, Try, Unwrap, UnwrapErr};
use crate::words::consensus_buff::{FromConsensusBuff, ToConsensusBuff};
use crate::words::control_flow::{Begin, UnwrapErrPanic, UnwrapPanic};
use crate::words::conversion::{IntToAscii, IntToUtf8, StringToInt, StringToUint};
use crate::words::data_vars::{GetDataVar, SetDataVar};
use crate::words::default_to::DefaultTo;
use crate::words::enums::{ClarityErr, ClarityOk, ClaritySome};
use crate::words::equal::IsEq;
use crate::words::hashing::{Hash160, Keccak256, Sha256, Sha512, Sha512_256};
use crate::words::index_of::IndexOf;
use crate::words::logical::Not;
use crate::words::maps::{MapDelete, MapGet, MapInsert, MapSet};
use crate::words::noop::{ToInt, ToUint};
use crate::words::options::{IsNone, IsSome};
use crate::words::principal::{Construct, Destruct, IsStandard};
use crate::words::print::Print;
use crate::words::responses::{IsErr, IsOk};
use crate::words::secp256k1::Decompress;
use crate::words::sequences::{
    Append, AsMaxLen, Concat, ElementAt, Fold, Len, ListCons, Map, ReplaceAt, Slice,
};
use crate::words::to_ascii::ToAscii;
use crate::words::tuples::{TupleCons, TupleGet, TupleMerge};
use crate::words::{ed25519, secp256k1, secp256r1, Word};

lazy_static! {
    /// Costs for Clarity 6, as defined by `Costs5` in the interpreter.
    ///
    /// `Costs5` is a full recalibration rather than an extension of `Costs4`: every entry
    /// below overrides the value inherited from [`clar4`]. Words whose cost function still
    /// forwards to `Costs4` in the interpreter (contract calls, block info, STX and token
    /// operations, `as-contract`, `contract-hash`, `restrict-assets`, `as-contract-safe`,
    /// ...) are intentionally absent here and keep their Clarity 4 cost.
    pub(super) static ref WORD_COSTS: HashMap<ClarityName, WordCost> = {
        use Caf::*;

        let mut map = clar4::WORD_COSTS.clone();
        
        map.insert(
            Add.name(),
            WordCost {
                runtime: ShiftedLinear { shift: 4, a: 1, b: 31 },
                read_count: None,
                read_length: None,
                write_count: None,
                write_length: None,
            },
        );
        map.insert(
            Sub.name(),
            WordCost {
                runtime: ShiftedLinear { shift: 5, a: 1, b: 32 },
                read_count: None,
                read_length: None,
                write_count: None,
                write_length: None,
            },
        );
        map.insert(
            Mul.name(),
            WordCost {
                runtime: ShiftedLinear { shift: 4, a: 1, b: 31 },
                read_count: None,
                read_length: None,
                write_count: None,
                write_length: None,
            },
        );
        map.insert(
            Div.name(),
            WordCost {
                runtime: ShiftedLinear { shift: 5, a: 1, b: 32 },
                read_count: None,
                read_length: None,
                write_count: None,
                write_length: None,
            },
        );
        map.insert(
            Log2.name(),
            WordCost {
                runtime: Constant(31),
                read_count: None,
                read_length: None,
                write_count: None,
                write_length: None,
            },
        );
        map.insert(
            Modulo.name(),
            WordCost {
                runtime: Constant(31),
                read_count: None,
                read_length: None,
                write_count: None,
                write_length: None,
            },
        );
        map.insert(
            Power.name(),
            WordCost {
                runtime: Constant(31),
                read_count: None,
                read_length: None,
                write_count: None,
                write_length: None,
            },
        );
        map.insert(
            Sqrti.name(),
            WordCost {
                runtime: Constant(31),
                read_count: None,
                read_length: None,
                write_count: None,
                write_length: None,
            },
        );
        map.insert(
            BitwiseAnd.name(),
            WordCost {
                runtime: ShiftedLinear { shift: 4, a: 1, b: 31 },
                read_count: None,
                read_length: None,
                write_count: None,
                write_length: None,
            },
        );
        map.insert(
            BitwiseOr.name(),
            WordCost {
                runtime: ShiftedLinear { shift: 4, a: 1, b: 31 },
                read_count: None,
                read_length: None,
                write_count: None,
                write_length: None,
            },
        );
        map.insert(
            BitwiseXor.name(),
            WordCost {
                runtime: ShiftedLinear { shift: 4, a: 1, b: 31 },
                read_count: None,
                read_length: None,
                write_count: None,
                write_length: None,
            },
        );
        map.insert(
            BitwiseNot.name(),
            WordCost {
                runtime: Constant(31),
                read_count: None,
                read_length: None,
                write_count: None,
                write_length: None,
            },
        );
        map.insert(
            BitwiseLShift.name(),
            WordCost {
                runtime: Constant(31),
                read_count: None,
                read_length: None,
                write_count: None,
                write_length: None,
            },
        );
        map.insert(
            BitwiseRShift.name(),
            WordCost {
                runtime: Constant(31),
                read_count: None,
                read_length: None,
                write_count: None,
                write_length: None,
            },
        );
        map.insert(
            CmpGreater.name(),
            WordCost {
                runtime: ShiftedLinear { shift: 8, a: 1, b: 38 },
                read_count: None,
                read_length: None,
                write_count: None,
                write_length: None,
            },
        );
        map.insert(
            CmpGeq.name(),
            WordCost {
                runtime: ShiftedLinear { shift: 8, a: 1, b: 38 },
                read_count: None,
                read_length: None,
                write_count: None,
                write_length: None,
            },
        );
        map.insert(
            CmpLess.name(),
            WordCost {
                runtime: ShiftedLinear { shift: 8, a: 1, b: 38 },
                read_count: None,
                read_length: None,
                write_count: None,
                write_length: None,
            },
        );
        map.insert(
            CmpLeq.name(),
            WordCost {
                runtime: ShiftedLinear { shift: 8, a: 1, b: 38 },
                read_count: None,
                read_length: None,
                write_count: None,
                write_length: None,
            },
        );
        map.insert(
            Or.name(),
            WordCost {
                runtime: ShiftedLinear { shift: 4, a: 1, b: 31 },
                read_count: None,
                read_length: None,
                write_count: None,
                write_length: None,
            },
        );
        map.insert(
            And.name(),
            WordCost {
                runtime: ShiftedLinear { shift: 4, a: 1, b: 31 },
                read_count: None,
                read_length: None,
                write_count: None,
                write_length: None,
            },
        );
        map.insert(
            Not.name(),
            WordCost {
                runtime: Constant(31),
                read_count: None,
                read_length: None,
                write_count: None,
                write_length: None,
            },
        );
        map.insert(
            IsEq.name(),
            WordCost {
                runtime: ShiftedLinear { shift: 9, a: 1, b: 38 },
                read_count: None,
                read_length: None,
                write_count: None,
                write_length: None,
            },
        );
        map.insert(
            BuffToIntLe.name(),
            WordCost {
                runtime: Constant(31),
                read_count: None,
                read_length: None,
                write_count: None,
                write_length: None,
            },
        );
        map.insert(
            BuffToIntBe.name(),
            WordCost {
                runtime: Constant(31),
                read_count: None,
                read_length: None,
                write_count: None,
                write_length: None,
            },
        );
        map.insert(
            BuffToUintLe.name(),
            WordCost {
                runtime: Constant(31),
                read_count: None,
                read_length: None,
                write_count: None,
                write_length: None,
            },
        );
        map.insert(
            BuffToUintBe.name(),
            WordCost {
                runtime: Constant(31),
                read_count: None,
                read_length: None,
                write_count: None,
                write_length: None,
            },
        );
        map.insert(
            IntToAscii.name(),
            WordCost {
                runtime: Constant(31),
                read_count: None,
                read_length: None,
                write_count: None,
                write_length: None,
            },
        );
        map.insert(
            IntToUtf8.name(),
            WordCost {
                runtime: Constant(31),
                read_count: None,
                read_length: None,
                write_count: None,
                write_length: None,
            },
        );
        map.insert(
            StringToInt.name(),
            WordCost {
                runtime: ShiftedLinear { shift: 4, a: 1, b: 31 },
                read_count: None,
                read_length: None,
                write_count: None,
                write_length: None,
            },
        );
        map.insert(
            StringToUint.name(),
            WordCost {
                runtime: ShiftedLinear { shift: 4, a: 1, b: 31 },
                read_count: None,
                read_length: None,
                write_count: None,
                write_length: None,
            },
        );
        map.insert(
            ToInt.name(),
            WordCost {
                runtime: Constant(31),
                read_count: None,
                read_length: None,
                write_count: None,
                write_length: None,
            },
        );
        map.insert(
            ToUint.name(),
            WordCost {
                runtime: Constant(31),
                read_count: None,
                read_length: None,
                write_count: None,
                write_length: None,
            },
        );
        map.insert(
            ToAscii.name(),
            WordCost {
                runtime: ShiftedLinear { shift: 6, a: 1, b: 32 },
                read_count: None,
                read_length: None,
                write_count: None,
                write_length: None,
            },
        );
        map.insert(
            Hash160.name(),
            WordCost {
                runtime: ShiftedLinear { shift: 9, a: 1, b: 38 },
                read_count: None,
                read_length: None,
                write_count: None,
                write_length: None,
            },
        );
        map.insert(
            Keccak256.name(),
            WordCost {
                runtime: ShiftedLinear { shift: 9, a: 1, b: 38 },
                read_count: None,
                read_length: None,
                write_count: None,
                write_length: None,
            },
        );
        map.insert(
            Sha256.name(),
            WordCost {
                runtime: ShiftedLinear { shift: 9, a: 1, b: 38 },
                read_count: None,
                read_length: None,
                write_count: None,
                write_length: None,
            },
        );
        map.insert(
            Sha512.name(),
            WordCost {
                runtime: ShiftedLinear { shift: 9, a: 1, b: 38 },
                read_count: None,
                read_length: None,
                write_count: None,
                write_length: None,
            },
        );
        map.insert(
            Sha512_256.name(),
            WordCost {
                runtime: ShiftedLinear { shift: 9, a: 1, b: 38 },
                read_count: None,
                read_length: None,
                write_count: None,
                write_length: None,
            },
        );
        map.insert(
            secp256k1::Recover.name(),
            WordCost {
                runtime: Constant(38),
                read_count: None,
                read_length: None,
                write_count: None,
                write_length: None,
            },
        );
        map.insert(
            secp256k1::Verify.name(),
            WordCost {
                runtime: Constant(38),
                read_count: None,
                read_length: None,
                write_count: None,
                write_length: None,
            },
        );
        map.insert(
            secp256r1::Verify.name(),
            WordCost {
                runtime: Constant(38),
                read_count: None,
                read_length: None,
                write_count: None,
                write_length: None,
            },
        );
        map.insert(
            Construct.name(),
            WordCost {
                runtime: Constant(32),
                read_count: None,
                read_length: None,
                write_count: None,
                write_length: None,
            },
        );
        map.insert(
            Destruct.name(),
            WordCost {
                runtime: Constant(32),
                read_count: None,
                read_length: None,
                write_count: None,
                write_length: None,
            },
        );
        map.insert(
            IsStandard.name(),
            WordCost {
                runtime: Constant(31),
                read_count: None,
                read_length: None,
                write_count: None,
                write_length: None,
            },
        );
        map.insert(
            Let.name(),
            WordCost {
                runtime: ShiftedLinear { shift: 3, a: 1, b: 32 },
                read_count: None,
                read_length: None,
                write_count: None,
                write_length: None,
            },
        );
        map.insert(
            Begin.name(),
            WordCost {
                runtime: ShiftedLinear { shift: 4, a: 1, b: 31 },
                read_count: None,
                read_length: None,
                write_count: None,
                write_length: None,
            },
        );
        map.insert(
            Match.name(),
            WordCost {
                runtime: Constant(31),
                read_count: None,
                read_length: None,
                write_count: None,
                write_length: None,
            },
        );
        map.insert(
            Try.name(),
            WordCost {
                runtime: Constant(31),
                read_count: None,
                read_length: None,
                write_count: None,
                write_length: None,
            },
        );
        map.insert(
            Unwrap.name(),
            WordCost {
                runtime: Constant(31),
                read_count: None,
                read_length: None,
                write_count: None,
                write_length: None,
            },
        );
        map.insert(
            UnwrapErr.name(),
            WordCost {
                runtime: Constant(31),
                read_count: None,
                read_length: None,
                write_count: None,
                write_length: None,
            },
        );
        map.insert(
            UnwrapPanic.name(),
            WordCost {
                runtime: Constant(31),
                read_count: None,
                read_length: None,
                write_count: None,
                write_length: None,
            },
        );
        map.insert(
            UnwrapErrPanic.name(),
            WordCost {
                runtime: Constant(31),
                read_count: None,
                read_length: None,
                write_count: None,
                write_length: None,
            },
        );
        map.insert(
            DefaultTo.name(),
            WordCost {
                runtime: Constant(31),
                read_count: None,
                read_length: None,
                write_count: None,
                write_length: None,
            },
        );
        map.insert(
            ClarityOk.name(),
            WordCost {
                runtime: Constant(31),
                read_count: None,
                read_length: None,
                write_count: None,
                write_length: None,
            },
        );
        map.insert(
            ClarityErr.name(),
            WordCost {
                runtime: Constant(31),
                read_count: None,
                read_length: None,
                write_count: None,
                write_length: None,
            },
        );
        map.insert(
            ClaritySome.name(),
            WordCost {
                runtime: Constant(31),
                read_count: None,
                read_length: None,
                write_count: None,
                write_length: None,
            },
        );
        map.insert(
            IsOk.name(),
            WordCost {
                runtime: Constant(31),
                read_count: None,
                read_length: None,
                write_count: None,
                write_length: None,
            },
        );
        map.insert(
            IsErr.name(),
            WordCost {
                runtime: Constant(31),
                read_count: None,
                read_length: None,
                write_count: None,
                write_length: None,
            },
        );
        map.insert(
            IsNone.name(),
            WordCost {
                runtime: Constant(31),
                read_count: None,
                read_length: None,
                write_count: None,
                write_length: None,
            },
        );
        map.insert(
            IsSome.name(),
            WordCost {
                runtime: Constant(31),
                read_count: None,
                read_length: None,
                write_count: None,
                write_length: None,
            },
        );
        map.insert(
            Append.name(),
            WordCost {
                runtime: ShiftedLinear { shift: 4, a: 1, b: 31 },
                read_count: None,
                read_length: None,
                write_count: None,
                write_length: None,
            },
        );
        map.insert(
            AsMaxLen.name(),
            WordCost {
                runtime: Constant(31),
                read_count: None,
                read_length: None,
                write_count: None,
                write_length: None,
            },
        );
        map.insert(
            Concat.name(),
            WordCost {
                runtime: ShiftedLinear { shift: 10, a: 1, b: 31 },
                read_count: None,
                read_length: None,
                write_count: None,
                write_length: None,
            },
        );
        map.insert(
            ElementAt::Original.name(),
            WordCost {
                runtime: Constant(31),
                read_count: None,
                read_length: None,
                write_count: None,
                write_length: None,
            },
        );
        map.insert(
            ElementAt::Alias.name(),
            WordCost {
                runtime: Constant(31),
                read_count: None,
                read_length: None,
                write_count: None,
                write_length: None,
            },
        );
        map.insert(
            Filter.name(),
            WordCost {
                runtime: ShiftedLinear { shift: 2, a: 1, b: 32 },
                read_count: None,
                read_length: None,
                write_count: None,
                write_length: None,
            },
        );
        map.insert(
            Fold.name(),
            WordCost {
                runtime: ShiftedLinear { shift: 3, a: 1, b: 32 },
                read_count: None,
                read_length: None,
                write_count: None,
                write_length: None,
            },
        );
        map.insert(
            IndexOf::Original.name(),
            WordCost {
                runtime: ShiftedLinear { shift: 9, a: 1, b: 38 },
                read_count: None,
                read_length: None,
                write_count: None,
                write_length: None,
            },
        );
        map.insert(
            IndexOf::Alias.name(),
            WordCost {
                runtime: ShiftedLinear { shift: 9, a: 1, b: 38 },
                read_count: None,
                read_length: None,
                write_count: None,
                write_length: None,
            },
        );
        map.insert(
            Len.name(),
            WordCost {
                runtime: Constant(31),
                read_count: None,
                read_length: None,
                write_count: None,
                write_length: None,
            },
        );
        map.insert(
            ListCons.name(),
            WordCost {
                runtime: ShiftedLinear { shift: 4, a: 1, b: 31 },
                read_count: None,
                read_length: None,
                write_count: None,
                write_length: None,
            },
        );
        map.insert(
            Map.name(),
            WordCost {
                runtime: ShiftedLinear { shift: 2, a: 1, b: 32 },
                read_count: None,
                read_length: None,
                write_count: None,
                write_length: None,
            },
        );
        map.insert(
            ReplaceAt.name(),
            WordCost {
                runtime: ShiftedLinear { shift: 9, a: 1, b: 31 },
                read_count: None,
                read_length: None,
                write_count: None,
                write_length: None,
            },
        );
        map.insert(
            Slice.name(),
            WordCost {
                runtime: ShiftedLinear { shift: 9, a: 1, b: 38 },
                read_count: None,
                read_length: None,
                write_count: None,
                write_length: None,
            },
        );
        map.insert(
            TupleCons.name(),
            WordCost {
                runtime: ShiftedLinear { shift: 2, a: 1, b: 31 },
                read_count: None,
                read_length: None,
                write_count: None,
                write_length: None,
            },
        );
        map.insert(
            TupleGet.name(),
            WordCost {
                runtime: ShiftedLinear { shift: 2, a: 1, b: 32 },
                read_count: None,
                read_length: None,
                write_count: None,
                write_length: None,
            },
        );
        map.insert(
            TupleMerge.name(),
            WordCost {
                runtime: ShiftedLinear { shift: 2, a: 1, b: 32 },
                read_count: None,
                read_length: None,
                write_count: None,
                write_length: None,
            },
        );
        map.insert(
            ToConsensusBuff.name(),
            WordCost {
                runtime: ShiftedLinear { shift: 9, a: 1, b: 38 },
                read_count: None,
                read_length: None,
                write_count: None,
                write_length: None,
            },
        );
        map.insert(
            FromConsensusBuff.name(),
            WordCost {
                runtime: ShiftedLinear { shift: 9, a: 1, b: 38 },
                read_count: None,
                read_length: None,
                write_count: None,
                write_length: None,
            },
        );
        map.insert(
            Print.name(),
            WordCost {
                runtime: ShiftedLinear { shift: 9, a: 1, b: 31 },
                read_count: None,
                read_length: None,
                write_count: None,
                write_length: None,
            },
        );
        map.insert(
            GetDataVar.name(),
            WordCost {
                runtime: ShiftedLinear { shift: 9, a: 2, b: 44 },
                read_count: Constant(1),
                read_length: Linear { a: 1, b: 1 },
                write_count: None,
                write_length: None,
            },
        );
        map.insert(
            SetDataVar.name(),
            WordCost {
                runtime: ShiftedLinear { shift: 9, a: 4, b: 45 },
                // `clar3` and `clar4` are missing this read, even though
                // `cost_set_var` has charged it since Costs1.
                read_count: Constant(1),
                read_length: None,
                write_count: Constant(1),
                write_length: Linear { a: 1, b: 1 },
            },
        );
        map.insert(
            MapGet.name(),
            WordCost {
                runtime: Constant(44),
                read_count: Constant(1),
                read_length: Linear { a: 1, b: 1 },
                write_count: None,
                write_length: None,
            },
        );
        map.insert(
            MapSet.name(),
            WordCost {
                runtime: ShiftedLinear { shift: 9, a: 3, b: 45 },
                read_count: Constant(1),
                read_length: None,
                write_count: Constant(1),
                write_length: Linear { a: 1, b: 1 },
            },
        );
        map.insert(
            MapInsert.name(),
            WordCost {
                runtime: ShiftedLinear { shift: 9, a: 3, b: 45 },
                read_count: Constant(1),
                read_length: None,
                write_count: Constant(1),
                write_length: Linear { a: 1, b: 1 },
            },
        );
        map.insert(
            MapDelete.name(),
            WordCost {
                runtime: ShiftedLinear { shift: 9, a: 3, b: 45 },
                read_count: Constant(1),
                read_length: None,
                write_count: Constant(1),
                write_length: Linear { a: 1, b: 1 },
            },
        );
        map.insert(
            VerifyMerkleProof.name(),
            WordCost {
                runtime: ShiftedLinear { shift: 2, a: 1, b: 38 },
                read_count: None,
                read_length: None,
                write_count: None,
                write_length: None,
            },
        );
        map.insert(
            GetTxOutput.name(),
            WordCost {
                runtime: ShiftedLinear { shift: 9, a: 1, b: 38 },
                read_count: None,
                read_length: None,
                write_count: None,
                write_length: None,
            },
        );
        map.insert(
            ed25519::Verify.name(),
            WordCost {
                runtime: ShiftedLinear { shift: 9, a: 1, b: 39 },
                read_count: None,
                read_length: None,
                write_count: None,
                write_length: None,
            },
        );
        map.insert(
            Decompress.name(),
            WordCost {
                runtime: Constant(39),
                read_count: None,
                read_length: None,
                write_count: None,
                write_length: None,
            },
        );

        map
    };
}
