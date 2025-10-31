//! Convenience macros for declaring a group out of a function declaration.

#![deny(rustdoc::broken_intra_doc_links)]
#![deny(missing_debug_implementations)]
#![deny(missing_docs)]

use proc_macro::TokenStream;
use syn::{DeriveInput, ItemFn, parse_macro_input};

mod decompose;
mod group;

/// Creates a group annotation around the body of a function.
///
/// Functions annotated this way must have an argument that implements the
/// layouter trait. By default an argument named `layouter` is considered to be
/// that argument since that's the convention. If the argument has a different
/// name it must be annotated with `#[layouter]` such that the macro can locate
/// it.
///
/// The inputs and outputs of the gruop are derived from the arguments of the
/// function and its return value. The return value of the function is always
/// annotated as an output and arguments can be annotated with `#[input]` and/or
/// `#[output]` to signify the kind of IO they represent.
///
/// Any type that is treated as IO of the group must implement the
/// `DecomposeInCells` trait since the macro will rely on that trait for making
/// the annotations.
///
/// # Example
///
/// ```no_run
/// #[picus::group]
/// fn foo(&self, layouter: &mut impl Layouter<F>, inputs: #[input] &[AssignedNative<F>]) ->
/// Result<AssignedNative<F>, Error> {
///     // The body of this function is now wrapped in a call to `layouter.group()`.
///     inputs.iter().try_fold(F::ZERO, |acc, i| self.bar(layouter, i, acc))
///     // The return value is annotated as an output and gets forwarded untouched.
/// }
/// ```
#[proc_macro_attribute]
pub fn group(_: TokenStream, item: TokenStream) -> TokenStream {
    match group::group_impl(parse_macro_input!(item as ItemFn)) {
        Ok(tok) => tok,
        Err(err) => err.to_compile_error(),
    }
    .into()
}

/// Derive macro for the `DecomposeInCells` trait.
///
/// Requires that every inner element implements the trait and only structs are
/// currently supported.
#[proc_macro_derive(DecomposeInCells)]
pub fn derive_decompose_in_cells(input: TokenStream) -> TokenStream {
    decompose::derive_decompose_in_cells_impl(parse_macro_input!(input as DeriveInput)).into()
}
