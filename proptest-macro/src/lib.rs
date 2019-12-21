// -
// Copyright 2019 The proptest developers
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

extern crate proc_macro;

use proc_macro as pm;
use proc_macro2 as pm2;

#[proc_macro_attribute]
pub fn proptest(
    attr: pm::TokenStream,
    item: pm::TokenStream,
) -> pm::TokenStream {
    proptest_impl(attr.into(), item.into())
        .unwrap_or_else(|e| e.to_compile_error())
        .into()
}

fn proptest_impl(
    attr: pm2::TokenStream,
    item: pm2::TokenStream,
) -> Result<pm2::TokenStream, syn::Error> {
    let attr_args = syn::parse2(attr)?;
    syn::parse2(item.clone())
        .and_then(|item_fn| proptest_item_fn(item_fn, attr_args))
        .map(quote::ToTokens::into_token_stream)
        .map_err(|mut e| {
            e.combine(syn::Error::new_spanned(
                item,
                "`proptest` attribute can only be applied to fn items",
            ));
            e
        })
}

/// Transform the given function into a proptest test function.
fn proptest_item_fn(
    mut item_fn: syn::ItemFn,
    attr_args: AttrArgs,
) -> Result<syn::ItemFn, syn::Error> {
    let params = Params::new(&item_fn.sig.inputs)?;

    let config = attr_args.config;
    let name = item_fn.sig.ident.clone();
    let strategy = params.strategy()?;
    let names = params.names()?;
    let pattern = params.pattern()?;
    let return_type = return_type_normalize(&item_fn.sig.output);
    let body_test = (*item_fn.block).clone();

    attrs_add_test(&mut item_fn.attrs);
    signature_clear(&mut item_fn.sig);

    item_fn.block = syn::parse_quote! {{
        let mut config: ::proptest::test_runner::Config =
            ::core::clone::Clone::clone(&#config);
        config.test_name = ::core::option::Option::Some(
            ::core::concat!(::core::module_path!(), "::",
                            ::core::stringify!(#name))
        );
        config.source_file = ::core::option::Option::Some(::core::file!());
        let mut runner = ::proptest::test_runner::TestRunner::new(config);
        match runner.run(
            &::proptest::strategy::Strategy::prop_map(
                #strategy,
                |values| ::proptest::sugar::NamedArguments(#names, values),
            ),
            |::proptest::sugar::NamedArguments(_, #pattern)| {
                let testable: #return_type = #body_test;
                ::proptest::test_runner::Testable::result(testable)
            },
        ) {
            ::core::result::Result::Ok(_) => (),
            ::core::result::Result::Err(e) => {
                ::core::panic!("{}\n{}", e, runner);
            },
        };
    }};

    Ok(item_fn)
}

/// Parameters of a function annotated with a `proptest` attribute.
///
/// Used to extract token streams from the underlying parameter list.  For a
/// given parameter list, all extracted streams will be of the "same dimension".
#[derive(Debug, Eq, PartialEq)]
struct Params<'p> {
    params: &'p syn::punctuated::Punctuated<syn::FnArg, syn::Token![,]>,
    attr_strategy: syn::Path,
}

impl<'p> Params<'p> {
    /// Make a new instance containing the given parameter list.
    ///
    /// # Errors
    ///
    /// If the given parameter list is empty or contains parameters with
    /// unrecognized attributes.
    fn new(
        params: &'p syn::punctuated::Punctuated<syn::FnArg, syn::Token![,]>,
    ) -> Result<Self, syn::Error> {
        let attr_strategy = syn::parse_quote![strategy];
        if params.len() == 0 {
            return Err(syn::Error::new_spanned(
                params,
                "a proptest test must have at least one parameter",
            ));
        }
        for param in params {
            let attrs = match param {
                syn::FnArg::Receiver(receiver) => &receiver.attrs,
                syn::FnArg::Typed(pat_type) => &pat_type.attrs,
            };
            match attrs.iter().find(|attr| attr.path != attr_strategy) {
                Some(attr) => {
                    return Err(syn::Error::new_spanned(
                        attr,
                        "unrecognized parameter attribute",
                    ))
                }
                None => (),
            };
        }
        Ok(Self {
            params,
            attr_strategy,
        })
    }

    /// The stringified patterns of the parameters, as a string or as a tuple of
    /// strings.
    fn names(&self) -> Result<pm2::TokenStream, syn::Error> {
        Self::wrap_with(self.params.iter(), |pat_type| {
            let pat = &pat_type.pat;
            Ok(quote::quote![::core::stringify!(#pat)])
        })
    }

    /// The combined pattern of all the parameters, as a single pattern or as a
    /// tuple pattern of patterns.
    fn pattern(&self) -> Result<pm2::TokenStream, syn::Error> {
        Self::wrap_with(self.params.iter(), |pat_type| {
            let pat = &pat_type.pat;
            Ok(quote::quote![#pat])
        })
    }

    /// The combined strategy for all the parameters, as a tuple of strategies
    /// which produces values fitting the pattern obtained from [`pattern`].
    ///
    /// [`pattern`]: struct.Params.html#method.pattern
    fn strategy(&self) -> Result<pm2::TokenStream, syn::Error> {
        use quote::ToTokens;

        struct StrategyArg {
            _eq_token: syn::Token![=],
            expr: syn::Expr,
        }

        impl syn::parse::Parse for StrategyArg {
            fn parse(input: syn::parse::ParseStream) -> syn::Result<Self> {
                Ok(Self {
                    _eq_token: input.parse()?,
                    expr: input.parse()?,
                })
            }
        }

        Self::wrap_with(self.params.iter(), |pat_type| {
            let attrs = pat_type
                .attrs
                .iter()
                .filter(|attr| attr.path == self.attr_strategy)
                .collect::<Vec<_>>();
            match attrs.len() {
                0 => {
                    let ty = &pat_type.ty;
                    Ok(quote::quote![::proptest::arbitrary::any::<#ty>()])
                }
                1 => {
                    let strategy_arg: StrategyArg =
                        syn::parse2(attrs[0].tokens.clone())?;
                    Ok(strategy_arg.expr.into_token_stream())
                }
                _ => Err(syn::Error::new_spanned(
                    attrs[1],
                    "multiple `strategy` attributes for parameter",
                )),
            }
        })
    }

    fn wrap_with<F>(
        mut params: syn::punctuated::Iter<syn::FnArg>,
        mut map: F,
    ) -> Result<pm2::TokenStream, syn::Error>
    where
        F: FnMut(&syn::PatType) -> Result<pm2::TokenStream, syn::Error>,
    {
        use quote::ToTokens;

        let mut f = |fn_arg: &syn::FnArg| match fn_arg {
            syn::FnArg::Receiver(_) => Err(syn::Error::new_spanned(
                fn_arg,
                "unexpected receiver parameter",
            )),
            syn::FnArg::Typed(ref pat_type) => map(pat_type),
        };

        let mut stream = pm2::TokenStream::new();
        if params.len() == 1 {
            f(params.next().unwrap())?.to_tokens(&mut stream);
        } else {
            let elems: syn::punctuated::Punctuated<_, syn::Token![,]> =
                if params.len() <= Self::TUPLE_LEN_MAX {
                    params.map(f).collect::<Result<_, _>>()
                } else {
                    [f(params.next().unwrap()), Self::wrap_with(params, map)]
                        .into_iter()
                        .cloned()
                        .collect()
                }?;
            syn::token::Paren::default()
                .surround(&mut stream, |stream| elems.to_tokens(stream));
        };

        Ok(stream)
    }

    const TUPLE_LEN_MAX: usize = 10;
}

/// Normalize the return type of an fn item to the type is present, or `()`
/// otherwise.
fn return_type_normalize(return_type: &syn::ReturnType) -> syn::Type {
    use syn::ReturnType::*;
    match return_type {
        Default => syn::parse_quote![()],
        Type(_, ty) => (**ty).clone(),
    }
}

/// Add `#[test]` to the given sequence of attributes if it's not already
/// present in there.
fn attrs_add_test(attrs: &mut Vec<syn::Attribute>) {
    if attrs
        .iter()
        .find(|attr| attr.path == syn::parse_quote![test])
        .is_none()
    {
        attrs.push(syn::parse_quote![#[test]]);
    }
}

/// Clear the given signature, removing all parameters and the return type such
/// that it is suitable for a `#[test]` function.
fn signature_clear(signature: &mut syn::Signature) {
    signature.inputs = syn::punctuated::Punctuated::new();
    signature.output = syn::ReturnType::Default;
}

/// Arguments passed to the `proptest` attribute, as a list of the form:
///
/// ```ignore
/// #[proptest(ident_1 = expr_1, ident_2 = expr_2, ..., ident_n = expr_n)]
/// ```
///
/// Parsing only accepts recognized argument names, fails on duplicates of the
/// same argument, and stores a default expression for arguments which did not
/// appear in the list.
#[derive(Debug, Eq, PartialEq)]
struct AttrArgs {
    config: syn::Expr,
}

impl syn::parse::Parse for AttrArgs {
    fn parse(input: syn::parse::ParseStream) -> syn::Result<Self> {
        let mut config = None;

        let args = input.call(
            syn::punctuated::Punctuated::<AttrArg, syn::Token![,]>
                ::parse_terminated,
        )?;
        for arg in args {
            match &arg.ident.to_string()[..] {
                "config" => {
                    if config.is_none() {
                        config = Some(arg.expr);
                    } else {
                        return Err(syn::Error::new_spanned(
                            arg,
                            "multiple instances of attribute argument",
                        ));
                    }
                }
                _ => {
                    return Err(syn::Error::new_spanned(
                        arg,
                        "illegal attribute argument",
                    ))
                }
            }
        }

        Ok(Self {
            config: config
                .unwrap_or_else(|| syn::parse_quote![Default::default()]),
        })
    }
}

struct AttrArg {
    ident: syn::Ident,
    eq_token: syn::Token![=],
    expr: syn::Expr,
}

impl syn::parse::Parse for AttrArg {
    fn parse(input: syn::parse::ParseStream) -> syn::Result<Self> {
        Ok(Self {
            ident: input.parse()?,
            eq_token: input.parse()?,
            expr: input.parse()?,
        })
    }
}

impl quote::ToTokens for AttrArg {
    fn to_tokens(&self, tokens: &mut pm2::TokenStream) {
        self.ident.to_tokens(tokens);
        self.eq_token.to_tokens(tokens);
        self.expr.to_tokens(tokens);
    }
}

#[cfg(test)]
mod tests;
