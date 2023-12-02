use std::iter;

use quote::{__private::TokenStream, quote};
use syn::*;

const MSG_UNION: &str = "`RefCounted` cannot be derived on unions";
const MSG_ONCE_STRUCT: &str = "`RefCounted` requires exactly one field with `#[count_on]`";
const MSG_ONCE_VARIANT: &str =
    "`RefCounted` requires exactly one field with `#[count_on]` in each variant";

/// Automatically derives an implementation of `RefCounted` trait on the type.
///
/// See `RefCounted`'s trait documentation for more information.
#[proc_macro_derive(RefCounted, attributes(count_on))]
pub fn derive_ref_counted(ts: proc_macro::TokenStream) -> proc_macro::TokenStream {
    match derive_impl(parse_macro_input!(ts as DeriveInput)) {
        Ok(tokens) => tokens.into(),
        Err(error) => error.to_compile_error().into(),
    }
}

struct CountOn {
    ident: IdentOrIndex,
    ty: Type,
}

enum IdentOrIndex {
    Ident(Ident),
    Index(usize),
}

fn derive_generics(generics: &mut Generics, ty: &Type) {
    let pred = parse_quote!(#ty: owned_pin::sync::RefCounted);
    generics.make_where_clause().predicates.push(pred)
}

fn derive_fields(ident: &Ident, fields: Fields, msg: &str) -> Result<CountOn> {
    let pred_a = |attr: &Attribute| matches!(&attr.meta, Meta::Path(p) if p.is_ident("count_on"));
    let pred_f = |(_, field): &(usize, Field)| field.attrs.iter().any(pred_a);

    let fields: Vec<(usize, Field)> = fields.into_iter().enumerate().filter(pred_f).collect();
    match &*fields {
        [(ime, me)] => Ok(CountOn {
            ident: match me.ident.clone() {
                Some(ident) => IdentOrIndex::Ident(ident),
                None => IdentOrIndex::Index(*ime),
            },
            ty: me.ty.clone(),
        }),
        [] => Err(Error::new_spanned(ident, msg)),
        [_, (_, two), ..] => Err(match &two.ident {
            Some(ident) => Error::new_spanned(ident, msg),
            None => Error::new_spanned(&two.ty, msg),
        }),
    }
}

fn derive_variant(
    ident: &Ident,
    generics: &mut Generics,
    fields: Fields,
    msg: &str,
) -> Result<TokenStream> {
    let count_on = derive_fields(ident, fields, msg)?;
    derive_generics(generics, &count_on.ty);
    match count_on.ident {
        IdentOrIndex::Ident(fi) => Ok(quote! {
            #ident { #fi, .. } =>
            owned_pin::sync::RefCounted::ref_count(#fi)
        }),
        IdentOrIndex::Index(index) => {
            let before = iter::repeat_with(<Token![_]>::default).take(index);
            Ok(quote! {
                #ident (#(#before,)* field, ..) =>
                owned_pin::sync::RefCounted::ref_count(field)
            })
        }
    }
}

fn derive_struct(
    ident: &Ident,
    generics: &mut Generics,
    data: DataStruct,
) -> Result<Vec<TokenStream>> {
    derive_variant(ident, generics, data.fields, MSG_ONCE_STRUCT).map(|branch| vec![branch])
}

fn derive_enum(ident: &Ident, generics: &mut Generics, data: DataEnum) -> Result<Vec<TokenStream>> {
    let to_tokens = |variant: Variant| -> Result<TokenStream> {
        derive_variant(&variant.ident, generics, variant.fields, MSG_ONCE_VARIANT)
            .map(|tokens| quote! { #ident:: #tokens })
    };
    data.variants.into_iter().map(to_tokens).collect()
}

fn derive_impl(mut input: DeriveInput) -> Result<TokenStream> {
    let branches = match input.data {
        syn::Data::Struct(data) => derive_struct(&input.ident, &mut input.generics, data)?,
        syn::Data::Enum(data) => derive_enum(&input.ident, &mut input.generics, data)?,
        syn::Data::Union(_) => return Err(Error::new_spanned(input.ident, MSG_UNION)),
    };
    let ident = &input.ident;
    let (gimpl, gty, gwhere) = input.generics.split_for_impl();
    Ok(quote! {
        unsafe impl #gimpl owned_pin::sync::RefCounted for #ident #gty #gwhere {
            fn ref_count(&self) -> &owned_pin::sync::RefCount {
                match self { #(#branches,)* }
            }
        }
    })
}
