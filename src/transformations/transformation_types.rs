use std::cmp::Ordering;

#[derive(Clone)]
pub enum TransformationTypes {
    EQU,
    EXP,
    CON,
}

impl std::fmt::Display for TransformationTypes {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::EQU => f.write_fmt(format_args!("EQU")),
            Self::EXP => f.write_fmt(format_args!("EXP")),
            Self::CON => f.write_fmt(format_args!("CON")),
        }
    }
}

impl PartialEq for TransformationTypes {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (TransformationTypes::EQU, TransformationTypes::EQU) => true,
            (TransformationTypes::CON, TransformationTypes::CON) => true,
            (TransformationTypes::EXP, TransformationTypes::EXP) => true,
            _ => false,
        }
    }
}
impl PartialOrd for TransformationTypes {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        match (self, other) {
            (TransformationTypes::EQU, TransformationTypes::EQU) => Some(Ordering::Equal),
            (TransformationTypes::EQU, _) => Some(Ordering::Less),
            (_, TransformationTypes::EQU) => Some(Ordering::Greater),
            (_, _) => None,
        }
    }
}
