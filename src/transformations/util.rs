use nemo::rule_model::{
    components::{rule::Rule, statement::Statement},
    programs::{ProgramRead, handle::ProgramHandle},
};

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
