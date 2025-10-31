use clap::builder::PossibleValue;
use clap::ValueEnum;
use clarity::types::StacksEpochId;
use clarity::vm::ClarityVersion;

#[derive(Clone)]
pub struct WrappedEpochId(StacksEpochId);

impl Default for WrappedEpochId {
    fn default() -> WrappedEpochId {
        WrappedEpochId(StacksEpochId::Epoch25)
    }
}

impl From<WrappedEpochId> for StacksEpochId {
    fn from(epoch: WrappedEpochId) -> Self {
        epoch.0
    }
}

impl ValueEnum for WrappedEpochId {
    fn value_variants<'a>() -> &'a [Self] {
        &[
            WrappedEpochId(StacksEpochId::Epoch10),
            WrappedEpochId(StacksEpochId::Epoch20),
            WrappedEpochId(StacksEpochId::Epoch2_05),
            WrappedEpochId(StacksEpochId::Epoch21),
            WrappedEpochId(StacksEpochId::Epoch22),
            WrappedEpochId(StacksEpochId::Epoch23),
            WrappedEpochId(StacksEpochId::Epoch24),
            WrappedEpochId(StacksEpochId::Epoch25),
            WrappedEpochId(StacksEpochId::Epoch30),
            WrappedEpochId(StacksEpochId::Epoch31),
            WrappedEpochId(StacksEpochId::Epoch32),
            WrappedEpochId(StacksEpochId::Epoch33),
        ]
    }

    fn to_possible_value(&self) -> Option<PossibleValue> {
        match &self.0 {
            StacksEpochId::Epoch10 => Some(PossibleValue::new("1.0")),
            StacksEpochId::Epoch20 => Some(PossibleValue::new("2.0")),
            StacksEpochId::Epoch2_05 => Some(PossibleValue::new("2.05")),
            StacksEpochId::Epoch21 => Some(PossibleValue::new("2.1")),
            StacksEpochId::Epoch22 => Some(PossibleValue::new("2.2")),
            StacksEpochId::Epoch23 => Some(PossibleValue::new("2.3")),
            StacksEpochId::Epoch24 => Some(PossibleValue::new("2.4")),
            StacksEpochId::Epoch25 => Some(PossibleValue::new("2.5")),
            StacksEpochId::Epoch30 => Some(PossibleValue::new("3.0")),
            StacksEpochId::Epoch31 => Some(PossibleValue::new("3.1")),
            StacksEpochId::Epoch32 => Some(PossibleValue::new("3.2")),
            StacksEpochId::Epoch33 => Some(PossibleValue::new("3.3")),
        }
    }
}

#[derive(Clone)]
pub struct WrappedClarityVersion(ClarityVersion);

impl Default for WrappedClarityVersion {
    fn default() -> WrappedClarityVersion {
        WrappedClarityVersion(ClarityVersion::Clarity2)
    }
}

impl From<WrappedClarityVersion> for ClarityVersion {
    fn from(version: WrappedClarityVersion) -> Self {
        version.0
    }
}

impl ValueEnum for WrappedClarityVersion {
    fn value_variants<'a>() -> &'a [Self] {
        &[
            WrappedClarityVersion(ClarityVersion::Clarity1),
            WrappedClarityVersion(ClarityVersion::Clarity2),
            WrappedClarityVersion(ClarityVersion::Clarity3),
            WrappedClarityVersion(ClarityVersion::Clarity4),
        ]
    }

    fn to_possible_value(&self) -> Option<PossibleValue> {
        match &self.0 {
            ClarityVersion::Clarity1 => Some(PossibleValue::new("1")),
            ClarityVersion::Clarity2 => Some(PossibleValue::new("2")),
            ClarityVersion::Clarity3 => Some(PossibleValue::new("3")),
            ClarityVersion::Clarity4 => Some(PossibleValue::new("4")),
        }
    }
}
