//! Withholding of assigned cell values from developer-tool output.
//!
//! This module is compiled only with the feature `gpu`. Its helpers replace
//! every assigned, evaluated or lookup-input cell value with a fixed
//! placeholder, so that error text, debug output and tracing events cannot
//! carry witness values into logs. Gate names, regions, columns, rows and
//! constraint names are unaffected. Without the feature the call sites
//! compile the stock lines and the output is unchanged.

use group::ff::Field;

/// The text shown in place of a withheld cell value.
pub(super) const WITHHELD: &str = "<withheld>";

/// Returns the string to show for an already-formatted cell value.
pub(super) fn value_str(_value: &str) -> &str {
    WITHHELD
}

/// Formats an assigned cell value for developer-tool output.
pub(super) fn format_cell_value<F: Field>(_value: F) -> String {
    WITHHELD.to_string()
}

/// Scrubs an annotation that embeds a constant value.
///
/// The stock floor planners label constant assignments with the constant
/// itself (`Constant(...)`); every other annotation is returned unchanged.
pub(super) fn scrub_annotation(annotation: &str) -> String {
    if annotation.starts_with("Constant(") {
        format!("Constant({WITHHELD})")
    } else {
        annotation.to_string()
    }
}
