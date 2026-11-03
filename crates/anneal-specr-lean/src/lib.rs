//! Mechanical `specr lang` to Lean 4 transpiler, structural AST diff engine,
//! and correspondence gap code generator for upstream MiniRust specifications.

pub mod ast_diff;
pub mod expr_lower;
pub mod extractor;
pub mod gap_codegen;
pub mod lean_emit;
pub mod ops_emit;
pub mod sha256;
pub mod specr_ast;
pub mod type_env;
