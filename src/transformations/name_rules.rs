use nemo::rule_model::components::statement::Statement;
use nemo::rule_model::error::ValidationReport;
use nemo::rule_model::programs::handle::ProgramHandle;

use nemo::rule_model::pipeline::transformations::ProgramTransformation;
use nemo::rule_model::programs::{ProgramRead, ProgramWrite};

use crate::transformations::annotated_dependency_graphs::AnnotatedDependencyGraph;

/// Program transformation
/// For testing purposes
// #[derive(Debug, Clone, Copy, Default)]
pub struct TransformationNameRules{
    pub last_rule_name : u32,
}

impl TransformationNameRules {
    pub fn new() -> Self {
        Self { last_rule_name : 0 }
    }
    // Build the next rule name
    pub fn next_rule_name(&mut self) -> String {
        self.last_rule_name += 1;
        String::from("r_") + &self.last_rule_name.to_string()
    }
    
}

impl ProgramTransformation for TransformationNameRules {
    fn apply(mut self, program: &ProgramHandle) -> Result<ProgramHandle, ValidationReport> {
        let mut commit = program.fork();
        /* let a = strategy::RuleSelectionStrategy::new(rules);
        let b = strategy::SelectionStrategyError:: */

        program
            .statements()
            .enumerate()
            .for_each(|(ii, statement)| match statement {
                Statement::Rule(rule) => {
                    let mut new_rule = rule.clone();
                    let name = self.next_rule_name();
                    new_rule.set_name(name.as_str());
                    //println!("Name: {ii}, {:?}",new_rule.name());
                    //let new_new_rule = new_rule.clone();
                    //print!("{:?}",new_new_rule.name());
                    commit.add_rule(new_rule);
                }
                _ => commit.keep(statement),
            });
        println!("Renaming of rules complete");
        commit.submit()
    }
}
