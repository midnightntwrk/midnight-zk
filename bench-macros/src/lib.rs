extern crate proc_macro;
use proc_macro::TokenStream;
use quote::quote;
use syn::{FnArg, ItemFn, parse_macro_input};

#[proc_macro_attribute]
pub fn inner_bench(_attr: TokenStream, item: TokenStream) -> TokenStream {
    let mut input = parse_macro_input!(item as ItemFn);

    // Create new argument: `_group: &mut BenchmarkGroup<WallTime>`
    let arg: FnArg = syn::parse_quote! {
        _group: &mut ::criterion::BenchmarkGroup<::criterion::measurement::WallTime>
    };

    // Push it to the function's signature
    input.sig.inputs.push(arg);

    // Reconstruct function
    let output = quote! {
        #input
    };

    output.into()
}
