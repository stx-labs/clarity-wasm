use std::collections::HashMap;

use clarity::vm::types::TypeSignature;
use clarity::vm::{ClarityName, SymbolicExpression};
use lazy_static::lazy_static;
use walrus::InstrSeqBuilder;

use crate::{GeneratorError, WasmGenerator};

pub mod arithmetic;
pub mod bindings;
pub mod bitwise;
pub mod blockinfo;
pub mod buff_to_integer;
pub mod comparison;
pub mod conditionals;
pub mod consensus_buff;
pub mod constants;
pub mod contract;
pub mod control_flow;
pub mod conversion;
pub mod data_vars;
pub mod default_to;
pub mod enums;
pub mod equal;
pub mod functions;
pub mod hashing;
pub mod logical;
pub mod maps;
pub mod noop;
pub mod options;
pub mod principal;
pub mod print;
pub mod responses;
pub mod secp256k1;
pub mod sequences;
pub mod stx;
pub mod tokens;
pub mod traits;
pub mod tuples;

pub trait Word: Sync + core::fmt::Debug {
    fn name(&self) -> ClarityName;
}

pub trait ComplexWord: Word {
    fn traverse(
        &self,
        generator: &mut WasmGenerator,
        builder: &mut InstrSeqBuilder,
        _expr: &SymbolicExpression,
        args: &[SymbolicExpression],
    ) -> Result<(), GeneratorError>;
}

pub(crate) static COMPLEX_WORDS: &[&'static dyn ComplexWord] = &[
    &bindings::Let,
    &blockinfo::AtBlock,
    &blockinfo::GetBlockInfo,
    &blockinfo::GetBurnBlockInfo,
    &blockinfo::GetStacksBlockInfo,
    &blockinfo::GetTenureInfo,
    &conditionals::And,
    &conditionals::Asserts,
    &conditionals::Filter,
    &conditionals::If,
    &conditionals::Match,
    &conditionals::Or,
    &conditionals::Try,
    &conditionals::Unwrap,
    &conditionals::UnwrapErr,
    &consensus_buff::FromConsensusBuff,
    &consensus_buff::ToConsensusBuff,
    &constants::DefineConstant,
    &contract::AsContract,
    &contract::ContractCall,
    &control_flow::Begin,
    &control_flow::UnwrapErrPanic,
    &control_flow::UnwrapPanic,
    &data_vars::DefineDataVar,
    &data_vars::GetDataVar,
    &data_vars::SetDataVar,
    &default_to::DefaultTo,
    &enums::ClarityErr,
    &enums::ClarityOk,
    &enums::ClaritySome,
    &equal::IndexOf::Alias,
    &equal::IndexOf::Original,
    &equal::IsEq,
    &functions::DefinePrivateFunction,
    &functions::DefinePublicFunction,
    &functions::DefineReadonlyFunction,
    &maps::MapDefinition,
    &maps::MapDelete,
    &maps::MapGet,
    &maps::MapInsert,
    &maps::MapSet,
    &noop::ContractOf,
    &options::IsNone,
    &options::IsSome,
    &principal::Construct,
    &principal::PrincipalOf,
    &print::Print,
    &responses::IsErr,
    &responses::IsOk,
    &secp256k1::Recover,
    &secp256k1::Verify,
    &sequences::Append,
    &sequences::AsMaxLen,
    &sequences::Concat,
    &sequences::ElementAt::Alias,
    &sequences::ElementAt::Original,
    &sequences::Fold,
    &sequences::Len,
    &sequences::ListCons,
    &sequences::Map,
    &sequences::ReplaceAt,
    &sequences::Slice,
    &stx::StxTransfer,
    &stx::StxTransferMemo,
    &tokens::BurnFungibleToken,
    &tokens::BurnNonFungibleToken,
    &tokens::DefineFungibleToken,
    &tokens::DefineNonFungibleToken,
    &tokens::GetBalanceOfFungibleToken,
    &tokens::GetOwnerOfNonFungibleToken,
    &tokens::GetSupplyOfFungibleToken,
    &tokens::MintFungibleToken,
    &tokens::MintNonFungibleToken,
    &tokens::TransferFungibleToken,
    &tokens::TransferNonFungibleToken,
    &traits::DefineTrait,
    &traits::ImplTrait,
    &traits::UseTrait,
    &tuples::TupleCons,
    &tuples::TupleGet,
    &tuples::TupleMerge,
];

pub trait SimpleWord: Word {
    fn visit(
        &self,
        generator: &mut WasmGenerator,
        builder: &mut InstrSeqBuilder,
        arg_types: &[TypeSignature],
        return_type: &TypeSignature,
    ) -> Result<(), GeneratorError>;
}

pub(crate) static SIMPLE_WORDS: &[&'static dyn SimpleWord] = &[
    &arithmetic::Log2,
    &arithmetic::Modulo,
    &arithmetic::Power,
    &arithmetic::Sqrti,
    &bitwise::BitwiseAnd,
    &bitwise::BitwiseLShift,
    &bitwise::BitwiseNot,
    &bitwise::BitwiseOr,
    &bitwise::BitwiseRShift,
    &bitwise::BitwiseXor,
    &bitwise::Xor,
    &buff_to_integer::BuffToIntBe,
    &buff_to_integer::BuffToIntLe,
    &buff_to_integer::BuffToUintBe,
    &buff_to_integer::BuffToUintLe,
    &comparison::CmpGeq,
    &comparison::CmpGreater,
    &comparison::CmpLeq,
    &comparison::CmpLess,
    &conversion::IntToAscii,
    &conversion::IntToUtf8,
    &conversion::StringToInt,
    &conversion::StringToUint,
    &hashing::Hash160,
    &hashing::Keccak256,
    &hashing::Sha256,
    &hashing::Sha512,
    &hashing::Sha512_256,
    &logical::Not,
    &noop::ToInt,
    &noop::ToUint,
    &principal::Destruct,
    &principal::IsStandard,
    &stx::StxBurn,
    &stx::StxGetAccount,
    &stx::StxGetBalance,
];

pub(crate) static SIMPLE_VARIADIC_WORDS: &[&'static dyn SimpleWord] = &[
    &arithmetic::Sub,
    &arithmetic::Div,
    &arithmetic::Add,
    &arithmetic::Mul,
    &conditionals::SimpleOr,
    &conditionals::SimpleAnd,
];

lazy_static! {
    static ref COMPLEX_WORDS_BY_NAME: HashMap<ClarityName, &'static dyn ComplexWord> = {
        let mut cwbn = HashMap::new();

        for word in COMPLEX_WORDS {
            cwbn.insert(word.name(), &**word);
        }

        cwbn
    };
    static ref SIMPLE_WORDS_BY_NAME: HashMap<ClarityName, &'static dyn SimpleWord> = {
        let mut swbn = HashMap::new();

        for word in SIMPLE_WORDS {
            swbn.insert(word.name(), &**word);
        }

        swbn
    };
    static ref SIMPLE_VARIADIC_WORDS_BY_NAME: HashMap<ClarityName, &'static dyn SimpleWord> = {
        let mut svwbn = HashMap::new();

        for word in SIMPLE_VARIADIC_WORDS {
            svwbn.insert(word.name(), &**word);
        }

        svwbn
    };
}

pub fn lookup_complex(name: &str) -> Option<&'static dyn ComplexWord> {
    COMPLEX_WORDS_BY_NAME.get(name).copied()
}

pub fn lookup_simple(name: &str) -> Option<&'static dyn SimpleWord> {
    SIMPLE_WORDS_BY_NAME.get(name).copied()
}

pub fn lookup_variadic_simple(name: &str) -> Option<&'static dyn SimpleWord> {
    SIMPLE_VARIADIC_WORDS_BY_NAME.get(name).copied()
}

#[cfg(test)]
mod tests {
    use clarity::vm::analysis::type_checker::v2_1::TypedNativeFunction;
    use clarity::vm::functions::define::DefineFunctions;
    use clarity::vm::functions::NativeFunctions;
    use clarity::vm::variables::NativeVariables;

    #[test]
    fn check_for_duplicates() {
        use std::collections::HashSet;

        let mut names = HashSet::new();

        for word in super::COMPLEX_WORDS {
            assert!(
                names.insert(word.name()),
                "duplicate word: {:?}",
                word.name()
            );
        }

        for word in super::SIMPLE_WORDS {
            if word.name().as_str() != "or" && word.name().as_str() != "and" {
                assert!(
                    names.insert(word.name()),
                    "duplicate word: {:?}",
                    word.name()
                );
            }
        }
    }

    #[test]
    fn check_for_non_reserved_words() {
        for word in super::COMPLEX_WORDS {
            // Printing each word also gets us coverage on the Debug impl.
            println!("{:?} => {}", word, word.name());
            assert!(
                DefineFunctions::lookup_by_name(&word.name()).is_some()
                    || NativeFunctions::lookup_by_name(&word.name()).is_some()
                    || NativeVariables::lookup_by_name(&word.name()).is_some(),
            );
        }
        for word in super::SIMPLE_WORDS {
            // Printing each word also gets us coverage on the Debug impl.
            println!("{:?} => {}", word, word.name());
            assert!(
                DefineFunctions::lookup_by_name(&word.name()).is_some()
                    || NativeFunctions::lookup_by_name(&word.name()).is_some()
                    || NativeVariables::lookup_by_name(&word.name()).is_some(),
            );
        }
    }

    #[test]
    fn check_word_classes() {
        for word in super::SIMPLE_WORDS {
            if let Some(native) = NativeFunctions::lookup_by_name(word.name().as_str()) {
                if let Ok(TypedNativeFunction::Special(_)) =
                    TypedNativeFunction::type_native_function(&native)
                {
                    panic!("{word:?} should not be simple!")
                }
            }
        }

        for word in super::COMPLEX_WORDS {
            if let Some(native) = NativeFunctions::lookup_by_name(word.name().as_str()) {
                if let Ok(TypedNativeFunction::Simple(_)) =
                    TypedNativeFunction::type_native_function(&native)
                {
                    // we make some exeptions
                    if word.name().as_str() == "or" || word.name().as_str() == "and" {
                        continue;
                    }
                    panic!("{word:?} should not be complex!")
                }
            }
        }
    }
}
