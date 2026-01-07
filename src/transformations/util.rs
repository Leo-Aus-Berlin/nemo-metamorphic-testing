use nemo::rule_model::{
    components::{rule::Rule, statement::Statement},
    programs::{ProgramRead, handle::ProgramHandle},
};
use rand::seq::IteratorRandom;
use rand_chacha::ChaCha8Rng;

use crate::{DEBUG_MODE, NAME_OF_TRANSFORMATION_SEQUENCE};

pub fn fetch_rule_by_name(rule_name: String, program: &ProgramHandle) -> Option<&Rule> {
    for statement in program.statements() {
        match statement {
            Statement::Rule(rule) => {
                if let Some(rule_name_rule) = rule.name() {
                    if rule_name_rule == rule_name {
                        return Some(rule);
                    }
                }
            }
            _ => {}
        }
    }
    None
}

pub fn append_duplicates<T>(vec: &mut Vec<T>, rng: &mut ChaCha8Rng, amount: usize)
where
    T: Clone,
{
    let mut duplicates = vec.iter().cloned().choose_multiple(rng, amount);
    vec.append(&mut duplicates);
}

pub fn in_debug_mode() -> bool {
    DEBUG_MODE
        .get()
        .expect("Debug mode not initialised")
        .clone()
}

pub fn fetch_transformation_name() -> String {
    NAME_OF_TRANSFORMATION_SEQUENCE
        .get()
        .expect("Name of Transformation Sequence not set")
        .to_string()
}
