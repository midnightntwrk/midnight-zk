use proc_macro2::TokenStream;
use quote::quote;
use syn::{Data, DeriveInput, Fields, spanned::Spanned as _};

pub fn derive_decompose_in_cells_impl(input: DeriveInput) -> TokenStream {
    let name = input.ident;
    let generics = input.generics;

    // Split generics into (impl generics) (ty generics) (where clause)
    let (impl_generics, ty_generics, where_clause) = generics.split_for_impl();
    let body = match &input.data {
        Data::Struct(data) => match &data.fields {
            Fields::Named(fields) => {
                let field_calls = fields.named.iter().map(|f| {
                    let fname = &f.ident;
                    quote! { .chain(self.#fname.cells()) }
                });
                quote! {
                    fn cells(&self) -> impl IntoIterator<Item = midnight_proofs::circuit::Cell> {
                        std::iter::empty() #(#field_calls)*
                    }
                }
            }
            Fields::Unnamed(fields) => {
                let idx = (0..fields.unnamed.len()).map(syn::Index::from);
                let field_calls = idx.map(|i| quote! { .chain(self.#i.cells()) });
                quote! {
                    fn cells(&self) -> impl IntoIterator<Item = midnight_proofs::circuit::Cell> {
                        std::iter::empty() #(#field_calls)*
                    }
                }
            }
            Fields::Unit => {
                quote! {
                    fn cells(&self) -> impl IntoIterator<Item = midnight_proofs::circuit::Cell> {
                        std::iter::empty()
                    }
                }
            }
        },
        Data::Enum(data) => {
            let variants = data.variants.iter().map(|v| {
                let vname = &v.ident;
                match &v.fields {
                    Fields::Named(fields) => {
                        let fnames: Vec<_> =
                            fields.named.iter().map(|f| f.ident.as_ref().unwrap()).collect();
                        let chains = fnames.iter().map(|f| quote! { .chain(#f.cells()) });
                        quote! {
                            Self::#vname { #( #fnames ),* } => {
                                std::iter::empty() #(#chains)*
                            }
                        }
                    }
                    Fields::Unnamed(fields) => {
                        let vars: Vec<_> = (0..fields.unnamed.len())
                            .map(|i| syn::Ident::new(&format!("f{i}"), v.span()))
                            .collect();
                        let chains = vars.iter().map(|v| quote! { .chain(#v.cells()) });
                        quote! {
                            Self::#vname( #( #vars ),* ) => {
                                std::iter::empty() #(#chains)*
                            }
                        }
                    }
                    Fields::Unit => {
                        quote! {
                            Self::#vname => std::iter::empty(),
                        }
                    }
                }
            });

            quote! {
                fn cells(&self) -> impl IntoIterator<Item = midnight_proofs::circuit::Cell> {
                    match self {
                        #(#variants),*
                    }
                }
            }
        }
        Data::Union(_) => {
            unimplemented!("Unions are not supported")
        }
    };

    // Collect field types for where bounds
    let mut bounds = Vec::new();
    match &input.data {
        Data::Struct(data) => {
            for field in data.fields.iter() {
                let ty = &field.ty;
                bounds.push(quote! { #ty: picus_macros_support::DecomposeInCells });
            }
        }
        Data::Enum(data) => {
            for variant in &data.variants {
                for field in &variant.fields {
                    let ty = &field.ty;
                    bounds.push(quote! { #ty: picus_macros_support::DecomposeInCells });
                }
            }
        }
        Data::Union(_) => {}
    }

    quote! {
        impl #impl_generics picus_macros_support::DecomposeInCells for #name #ty_generics
        where
            #(#bounds,)*
            #where_clause
        {
            #body
        }
    }
}
