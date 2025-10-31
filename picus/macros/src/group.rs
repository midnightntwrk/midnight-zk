use proc_macro2::TokenStream;
use quote::{format_ident, quote};
use syn::{FnArg, ItemFn};

pub fn group_impl(input_fn: ItemFn) -> syn::Result<TokenStream> {
    let vis = &input_fn.vis;
    let fn_ident = &input_fn.sig.ident;
    let user_block = &input_fn.block;
    let fn_attrs = &input_fn.attrs;
    let output = &input_fn.sig.output;

    let group_ident = format_ident!("__{}__group", fn_ident);

    let input_annotations = input_fn.sig.inputs.iter().filter_map(|i| match i {
        FnArg::Receiver(_) => None,
        FnArg::Typed(pat_type) => {
            if pat_type
                .attrs
                .iter()
                .find(|attr| {
                    attr.path().get_ident().map(|ident| ident == "input").unwrap_or_default()
                })
                .is_some()
            {
                let pat = &pat_type.pat;
                Some(quote! { #pat.annotate_as_input(#group_ident)?; })
            } else {
                None
            }
        }
    });
    // Remove the extra attributes in the arguments since those are fake.
    let cleaned_inputs = input_fn.sig.inputs.iter().map(|i| match i {
        FnArg::Receiver(receiver) => FnArg::Receiver(receiver.clone()),
        FnArg::Typed(pat_type) => {
            let mut pat_type = pat_type.clone();
            pat_type.attrs.retain(|attr| {
                attr.path().get_ident().map(|ident| ident != "input").unwrap_or(true)
            });
            FnArg::Typed(pat_type)
        }
    });

    let expanded = quote! {
        // preserve doc/outer attributes except group attribute
        #(#fn_attrs)*
        #vis fn #fn_ident(#(#cleaned_inputs, )*) #output {

            layouter.group(|| stringify!(#fn_ident), midnight_proofs::default_group_key!(), |layouter,#[allow(non_snake_case)] #group_ident| {
                use picus_macros_support::DecomposeInCells as _;
                #(#input_annotations)*
                let inner_result = #user_block;
                inner_result.annotate_as_output(#group_ident)?;
                inner_result
            })
        }
    };

    Ok(expanded)
}
