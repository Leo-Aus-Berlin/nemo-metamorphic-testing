use std::cmp::Ordering;

#[derive(Clone)]
pub enum TransformationTypes {
    EQU,
    EXP,
    CON
}
impl PartialEq for TransformationTypes {
    fn eq(&self, other: &Self) -> bool {
        match (self,other) {
            (TransformationTypes::EQU,TransformationTypes::EQU) => true,
            (TransformationTypes::CON,TransformationTypes::CON) => true,
            (TransformationTypes::EXP,TransformationTypes::EXP) => true,
            _ => false
        }
    }
}
impl PartialOrd for TransformationTypes {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        match (self,other) {
            (TransformationTypes::EQU,TransformationTypes::EQU) => Some(Ordering::Equal),
            (TransformationTypes::EQU,_) => Some(Ordering::Less),
            (_,TransformationTypes::EQU) => Some(Ordering::Greater),
            (_,_) => None
        }
    }
}