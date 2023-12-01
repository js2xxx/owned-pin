use std::iter;

use quote::{quote, ToTokens, __private::TokenStream};
use syn::{punctuated::Punctuated, *};

const MSG_UNION: &str = "`RefCounted` cannot be derived on unions";
const MSG_ONCE_STRUCT: &str = "`RefCounted` requires exactly one field with `#[count_on]`";
const MSG_ONCE_VARIANT: &str =
    "`RefCounted` requires exactly one field with `#[count_on]` in each variant";

/// Automatically derives an implementation of `RefCounted` trait on the type.
///
/// See `RefCounted`'s trait documentation for more information.
#[proc_macro_derive(RefCounted, attributes(count_on))]
pub fn derive_ref_counted(ts: proc_macro::TokenStream) -> proc_macro::TokenStream {
    let input = parse_macro_input!(ts as DeriveInput);
    match input.data {
        syn::Data::Struct(data) => derive_struct(input.ident, data, MSG_ONCE_STRUCT).into(),
        syn::Data::Enum(data) => derive_enum(input.ident, data).into(),
        syn::Data::Union(_) => {
            let error = Error::new_spanned(input.ident, MSG_UNION);
            error.to_compile_error().into()
        }
    }
}

enum IdentOrIndex {
    Ident(Ident),
    Index(usize),
}

impl IdentOrIndex {
    fn unwrap_index(self) -> usize {
        match self {
            IdentOrIndex::Index(index) => index,
            IdentOrIndex::Ident(_) => unreachable!(),
        }
    }
}

impl ToTokens for IdentOrIndex {
    fn to_tokens(&self, tokens: &mut TokenStream) {
        match self {
            IdentOrIndex::Ident(ident) => ident.to_tokens(tokens),
            IdentOrIndex::Index(index) => quote!(#index).to_tokens(tokens),
        }
    }
}

fn derive_variant(ident: &Ident, fields: &Fields, msg: &str) -> Result<IdentOrIndex> {
    let pred_a = |attr: &Attribute| matches!(&attr.meta, Meta::Path(p) if p.is_ident("count_on"));
    let pred_f = |(_, field): &(usize, &Field)| field.attrs.iter().any(pred_a);

    let fields: Vec<(usize, &Field)> = fields.iter().enumerate().filter(pred_f).collect();
    match *fields {
        [(ime, me)] => Ok(match me.ident.clone() {
            Some(ident) => IdentOrIndex::Ident(ident),
            None => IdentOrIndex::Index(ime),
        }),
        [] => Err(Error::new_spanned(ident, msg)),
        [_, (_, two), ..] => Err(match &two.ident {
            Some(ident) => Error::new_spanned(ident, msg),
            None => Error::new_spanned(&two.ty, msg),
        }),
    }
}

fn derive_struct(ident: Ident, data: DataStruct, msg: &str) -> TokenStream {
    let count_on = match derive_variant(&ident, &data.fields, msg) {
        Ok(field) => field,
        Err(err) => return err.to_compile_error(),
    };
    quote! {
        unsafe impl owned_pin::sync::RefCounted for #ident {
            fn ref_count(&self) -> &owned_pin::sync::RefCount {
                owned_pin::sync::RefCounted::ref_count(&self. #count_on)
            }
        }
    }
}

fn derive_enum(ident: Ident, data: DataEnum) -> TokenStream {
    let to_tokens = |variant: &Variant| -> Result<TokenStream> {
        let vi = &variant.ident;
        let count_on = derive_variant(vi, &variant.fields, MSG_ONCE_VARIANT)?;
        match &variant.fields {
            Fields::Named(_) => Ok(quote! {
                #ident::#vi { #count_on, .. } =>
                owned_pin::sync::RefCounted::ref_count(#count_on)
            }),
            Fields::Unnamed(_) => {
                let count_on = count_on.unwrap_index();
                let punc = iter::repeat_with(<Token![_]>::default)
                    .take(count_on)
                    .collect::<Punctuated<Token![_], Token![,]>>();
                Ok(quote! {
                    #ident::#vi (#punc, field, ..) =>
                    owned_pin::sync::RefCounted::ref_count(field)
                })
            }
            Fields::Unit => unreachable!(),
        }
    };
    let branches: Vec<TokenStream> = match data.variants.iter().map(to_tokens).collect() {
        Ok(tokens) => tokens,
        Err(err) => return err.to_compile_error(),
    };
    quote! {
        unsafe impl owned_pin::sync::RefCounted for #ident {
            fn ref_count(&self) -> &owned_pin::sync::RefCount {
                match self { #(#branches),* }
            }
        }
    }
}
