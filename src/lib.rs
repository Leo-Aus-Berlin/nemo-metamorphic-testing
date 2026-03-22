use std::sync::OnceLock;

pub mod transformations;

pub static DEBUG_MODE: OnceLock<bool> = OnceLock::new();
