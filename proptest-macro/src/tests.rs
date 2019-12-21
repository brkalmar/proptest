// -
// Copyright 2019 The proptest developers
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

use super::*;
use std::fmt;

macro_rules! quote {
    ($($tt:tt)*) => {
        util::TokenStream::from(quote::quote![ $($tt)* ])
    }
}

mod proptest_item_fn {
    use super::{util, AttrArgs};

    #[test]
    fn minimal() {
        let actual = proptest_item_fn(
            syn::parse_quote! {
                fn xyz(a: u8) { }
            },
            syn::parse_quote![],
        );
        let expected = Ok(syn::parse_quote! {
            #[test]
            fn xyz() {
                let mut config: ::proptest::test_runner::Config =
                    ::core::clone::Clone::clone(&Default::default());
                config.test_name = ::core::option::Option::Some(
                    ::core::concat!(::core::module_path!(), "::",
                                    ::core::stringify!(xyz))
                );
                config.source_file =
                    ::core::option::Option::Some(::core::file!());
                let mut runner =
                    ::proptest::test_runner::TestRunner::new(config);
                match runner.run(
                    &::proptest::strategy::Strategy::prop_map(
                        ::proptest::arbitrary::any::<u8>(),
                        |values| ::proptest::sugar::NamedArguments(
                            ::core::stringify!(a),
                            values
                        ),
                    ),
                    |::proptest::sugar::NamedArguments(_, a)| {
                        let testable: () = { };
                        ::proptest::test_runner::Testable::result(testable)
                    },
                ) {
                    ::core::result::Result::Ok(_) => (),
                    ::core::result::Result::Err(e) => {
                        ::core::panic!("{}\n{}", e, runner);
                    },
                };
            }
        });
        assert_eq!(actual, expected);
    }

    #[test]
    fn full_short() {
        let actual = proptest_item_fn(
            syn::parse_quote! {
                #[test]
                fn zxcv(
                    #[strategy = S::with(7)]
                    a: u8,
                    #[strategy = (f(), g())]
                    (b_1, b_2): (String, char),
                    #[strategy = 15..=150]
                    c: u16
                ) -> Result<bool, io::Error> {
                    if uvw(a, b_1, c)? > 100 {
                        Ok(true)
                    } else {
                        Ok(false)
                    }
                }
            },
            syn::parse_quote! {
                config = ProptestConfig {
                    cases: 32,
                    timeout: 2_000,
                    .. Default::default()
                }
            },
        );
        let expected = Ok(syn::parse_quote! {
            #[test]
            fn zxcv() {
                let mut config: ::proptest::test_runner::Config =
                    ::core::clone::Clone::clone(&ProptestConfig {
                        cases: 32,
                        timeout: 2_000,
                        .. Default::default()
                    });
                config.test_name = ::core::option::Option::Some(
                    ::core::concat!(::core::module_path!(), "::",
                                    ::core::stringify!(zxcv))
                );
                config.source_file =
                    ::core::option::Option::Some(::core::file!());
                let mut runner =
                    ::proptest::test_runner::TestRunner::new(config);
                match runner.run(
                    &::proptest::strategy::Strategy::prop_map(
                        (S::with(7), (f(), g()), 15..=150),
                        |values| ::proptest::sugar::NamedArguments((
                            ::core::stringify!(a),
                            ::core::stringify!((b_1, b_2)),
                            ::core::stringify!(c)
                        ), values),
                    ),
                    |::proptest::sugar::NamedArguments(_, (a, (b_1, b_2), c))| {
                        let testable: Result<bool, io::Error> = {
                            if uvw(a, b_1, c)? > 100 {
                                Ok(true)
                            } else {
                                Ok(false)
                            }
                        };
                        ::proptest::test_runner::Testable::result(testable)
                    },
                ) {
                    ::core::result::Result::Ok(_) => (),
                    ::core::result::Result::Err(e) => {
                        ::core::panic!("{}\n{}", e, runner);
                    },
                };
            }
        });
        assert_eq!(actual, expected);
    }

    fn proptest_item_fn(
        item_fn: syn::ItemFn,
        attr_args: AttrArgs,
    ) -> Result<syn::ItemFn, util::Error> {
        super::proptest_item_fn(item_fn, attr_args).map_err(Into::into)
    }
}

mod params {
    use super::{fmt, util};

    #[test]
    fn single_simple_strategy_none() {
        let item_fn: syn::ItemFn = syn::parse_quote! {
            fn a(
                xub: u16,
            ) {}
        };
        let params = Params::new(&item_fn.sig.inputs);
        assert!(params.is_ok());
        let params = params.unwrap();

        assert_eq!(params.names(), Ok(quote![::core::stringify!(xub)]));
        assert_eq!(params.pattern(), Ok(quote![xub]));
        assert_eq!(
            params.strategy(),
            Ok(quote![::proptest::arbitrary::any::<u16>()])
        );
    }

    #[test]
    fn single_simple_strategy_one() {
        let item_fn: syn::ItemFn = syn::parse_quote! {
            fn a(
                #[strategy = zaaf()]
                xub: u16,
            ) {}
        };
        let params = Params::new(&item_fn.sig.inputs);
        assert!(params.is_ok());
        let params = params.unwrap();

        assert_eq!(params.names(), Ok(quote![::core::stringify!(xub)]));
        assert_eq!(params.pattern(), Ok(quote![xub]));
        assert_eq!(params.strategy(), Ok(quote![zaaf()]));
    }

    #[test]
    fn single_tuple_strategy_none() {
        let item_fn: syn::ItemFn = syn::parse_quote! {
            fn a(
                (xub, baz): (bool, char),
            ) {}
        };
        let params = Params::new(&item_fn.sig.inputs);
        assert!(params.is_ok());
        let params = params.unwrap();

        assert_eq!(params.names(), Ok(quote![::core::stringify!((xub, baz))]));
        assert_eq!(params.pattern(), Ok(quote![(xub, baz)]));
        assert_eq!(
            params.strategy(),
            Ok(quote![::proptest::arbitrary::any::<(bool, char)>()])
        );
    }

    #[test]
    fn single_tuple_strategy_one() {
        let item_fn: syn::ItemFn = syn::parse_quote! {
            fn a(
                #[strategy = (first(), second())]
                (xub, baz): (bool, char),
            ) {}
        };
        let params = Params::new(&item_fn.sig.inputs);
        assert!(params.is_ok());
        let params = params.unwrap();

        assert_eq!(params.names(), Ok(quote![::core::stringify!((xub, baz))]));
        assert_eq!(params.pattern(), Ok(quote![(xub, baz)]));
        assert_eq!(params.strategy(), Ok(quote![(first(), second())]));
    }

    #[test]
    fn short_strategy_none() {
        let item_fn: syn::ItemFn = syn::parse_quote! {
            fn a(
                aaa: u8,
                (bbb, ccc, ddd): (u16, String, i8),
                eee: char,
            ) {}
        };
        let params = Params::new(&item_fn.sig.inputs);
        assert!(params.is_ok());
        let params = params.unwrap();

        assert_eq!(
            params.names(),
            Ok(quote! {
                (::core::stringify!(aaa),
                 ::core::stringify!((bbb, ccc, ddd)),
                 ::core::stringify!(eee))
            })
        );
        assert_eq!(
            params.pattern(),
            Ok(quote! {
                (aaa, (bbb, ccc, ddd), eee)
            })
        );
        assert_eq!(
            params.strategy(),
            Ok(quote! {
                (::proptest::arbitrary::any::<u8>(),
                 ::proptest::arbitrary::any::<(u16, String, i8)>(),
                 ::proptest::arbitrary::any::<char>())
            })
        );
    }

    #[test]
    fn short_strategy_some() {
        let item_fn: syn::ItemFn = syn::parse_quote! {
            fn a(
                (aaa, bbb): (bool, Vec<u8>),
                ccc: char,
                #[strategy = f().g()]
                (ddd, eee): (Option<()>, i64),
                #[strategy = asdf]
                fff: char,
            ) {}
        };
        let params = Params::new(&item_fn.sig.inputs);
        assert!(params.is_ok());
        let params = params.unwrap();

        assert_eq!(
            params.names(),
            Ok(quote! {
                (::core::stringify!((aaa, bbb)),
                 ::core::stringify!(ccc),
                 ::core::stringify!((ddd, eee)),
                 ::core::stringify!(fff))
            })
        );
        assert_eq!(
            params.pattern(),
            Ok(quote! {
                ((aaa, bbb), ccc, (ddd, eee), fff)
            })
        );
        assert_eq!(
            params.strategy(),
            Ok(quote! {
                (::proptest::arbitrary::any::<(bool, Vec<u8>)>(),
                 ::proptest::arbitrary::any::<char>(),
                 f().g(),
                 asdf)
            })
        );
    }

    #[test]
    fn long_strategy_none() {
        let item_fn: syn::ItemFn = syn::parse_quote! {
            fn a(
                a: u8,
                b: Option<u8>,
                c: Option<i16>,
                d: i64,
                e: Option<i32>,
                f: u16,
                g: i16,
                h: String,
                i: bool,
                j: Option<bool>,
                (k, l): (u32, u64),
                m: i8,
                n: i32,
            ) {}
        };
        let params = Params::new(&item_fn.sig.inputs);
        assert!(params.is_ok());
        let params = params.unwrap();

        assert_eq!(
            params.names(),
            Ok(quote! {
                (::core::stringify!(a),
                 (::core::stringify!(b),
                  (::core::stringify!(c),
                   (::core::stringify!(d),
                    ::core::stringify!(e),
                    ::core::stringify!(f),
                    ::core::stringify!(g),
                    ::core::stringify!(h),
                    ::core::stringify!(i),
                    ::core::stringify!(j),
                    ::core::stringify!((k, l)),
                    ::core::stringify!(m),
                    ::core::stringify!(n)))))
            })
        );
        assert_eq!(
            params.pattern(),
            Ok(quote! {
                (a, (b, (c, (d, e, f, g, h, i, j, (k, l), m, n))))
            })
        );
        assert_eq!(
            params.strategy(),
            Ok(quote! {
                (::proptest::arbitrary::any::<u8>(),
                 (::proptest::arbitrary::any::<Option<u8> >(),
                  (::proptest::arbitrary::any::<Option<i16> >(),
                   (::proptest::arbitrary::any::<i64>(),
                    ::proptest::arbitrary::any::<Option<i32> >(),
                    ::proptest::arbitrary::any::<u16>(),
                    ::proptest::arbitrary::any::<i16>(),
                    ::proptest::arbitrary::any::<String>(),
                    ::proptest::arbitrary::any::<bool>(),
                    ::proptest::arbitrary::any::<Option<bool> >(),
                    ::proptest::arbitrary::any::<(u32, u64)>(),
                    ::proptest::arbitrary::any::<i8>(),
                    ::proptest::arbitrary::any::<i32>()))))
            })
        );
    }

    #[test]
    fn long_strategy_some() {
        let item_fn: syn::ItemFn = syn::parse_quote! {
            fn a(
                #[strategy = foo]
                a: u8,
                b: Option<u8>,
                #[strategy = prop::option::weighted(0.2, any())]
                c: Option<i16>,
                d: i64,
                e: Option<i32>,
                f: u16,
                g: i16,
                #[strategy = Bar::new()]
                h: String,
                #[strategy = macro_invocation!(1, 2, 3)]
                i: bool,
                j: Option<bool>,
                (k, l): (u32, u64),
                m: i8,
                n: i32,
            ) {}
        };
        let params = Params::new(&item_fn.sig.inputs);
        assert!(params.is_ok());
        let params = params.unwrap();

        assert_eq!(
            params.names(),
            Ok(quote! {
                (::core::stringify!(a),
                 (::core::stringify!(b),
                  (::core::stringify!(c),
                   (::core::stringify!(d),
                    ::core::stringify!(e),
                    ::core::stringify!(f),
                    ::core::stringify!(g),
                    ::core::stringify!(h),
                    ::core::stringify!(i),
                    ::core::stringify!(j),
                    ::core::stringify!((k, l)),
                    ::core::stringify!(m),
                    ::core::stringify!(n)))))
            })
        );
        assert_eq!(
            params.pattern(),
            Ok(quote! {
                (a, (b, (c, (d, e, f, g, h, i, j, (k, l), m, n))))
            })
        );
        assert_eq!(
            params.strategy(),
            Ok(quote! {
                (foo,
                 (::proptest::arbitrary::any::<Option<u8> >(),
                  (prop::option::weighted(0.2, any()),
                   (::proptest::arbitrary::any::<i64>(),
                    ::proptest::arbitrary::any::<Option<i32> >(),
                    ::proptest::arbitrary::any::<u16>(),
                    ::proptest::arbitrary::any::<i16>(),
                    Bar::new(),
                    macro_invocation!(1, 2, 3),
                    ::proptest::arbitrary::any::<Option<bool> >(),
                    ::proptest::arbitrary::any::<(u32, u64)>(),
                    ::proptest::arbitrary::any::<i8>(),
                    ::proptest::arbitrary::any::<i32>()))))
            })
        );
    }

    #[test]
    fn empty() {
        let item_fn: syn::ItemFn = syn::parse_quote! {
            fn a() {}
        };
        let params = Params::new(&item_fn.sig.inputs);
        assert_eq!(
            params,
            Err(util::Error::new(
                "a proptest test must have at least one parameter"
            ))
        );
    }

    #[test]
    fn unrecognized_attribute() {
        let item_fn: syn::ItemFn = syn::parse_quote! {
            fn a(
                aaa: [bool; 10],
                #[quux = "this attribute should be unrecognized"]
                bbb: i16,
                ccc: String,
            ) {}
        };
        let params = Params::new(&item_fn.sig.inputs);
        assert_eq!(
            params,
            Err(util::Error::new("unrecognized parameter attribute"))
        );
    }

    #[test]
    fn strategy_multiple() {
        let item_fn: syn::ItemFn = syn::parse_quote! {
            fn a(
                zuqq: i64,
                #[strategy = zaaf()]
                #[strategy = faaz()]
                xub: u16,
            ) {}
        };
        let params = Params::new(&item_fn.sig.inputs);
        assert!(params.is_ok());
        let params = params.unwrap();

        assert_eq!(
            params.strategy(),
            Err(util::Error::new(
                "multiple `strategy` attributes for parameter"
            ))
        );
    }

    #[derive(Eq, PartialEq)]
    struct Params<'p>(super::Params<'p>);

    impl<'p> Params<'p> {
        fn new(
            params: &'p syn::punctuated::Punctuated<syn::FnArg, syn::Token![,]>,
        ) -> Result<Self, util::Error> {
            super::Params::new(params).map(Self).map_err(Into::into)
        }

        fn names(&self) -> Result<util::TokenStream, util::Error> {
            self.0.names().map(Into::into).map_err(Into::into)
        }

        fn pattern(&self) -> Result<util::TokenStream, util::Error> {
            self.0.pattern().map(Into::into).map_err(Into::into)
        }

        fn strategy(&self) -> Result<util::TokenStream, util::Error> {
            self.0.strategy().map(Into::into).map_err(Into::into)
        }
    }

    impl<'p> fmt::Debug for Params<'p> {
        fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
            self.0.fmt(f)
        }
    }
}

mod return_type_normalize {
    use super::return_type_normalize;

    #[test]
    fn empty() {
        assert_eq!(
            return_type_normalize(&syn::parse_quote![]),
            syn::parse_quote![()]
        );
    }

    #[test]
    fn simple() {
        assert_eq!(
            return_type_normalize(&syn::parse_quote![-> char]),
            syn::parse_quote![char]
        );
    }

    #[test]
    fn complex() {
        assert_eq!(
            return_type_normalize(
                &syn::parse_quote![-> Result<(bool, i16), Option<io::Error>>]
            ),
            syn::parse_quote![Result<(bool, i16), Option<io::Error>>]
        );
    }
}

mod attrs_add_test {
    use super::attrs_add_test;

    #[test]
    fn empty() {
        let mut item_fn: syn::ItemFn = syn::parse_quote! {
            fn a() {}
        };
        attrs_add_test(&mut item_fn.attrs);
        assert_eq!(
            item_fn,
            syn::parse_quote! {
                #[test]
                fn a() {}
            }
        )
    }

    #[test]
    fn non_empty() {
        let mut item_fn: syn::ItemFn = syn::parse_quote! {
            #[foo]
            #[baz]
            fn a() {}
        };
        attrs_add_test(&mut item_fn.attrs);
        assert_eq!(
            item_fn,
            syn::parse_quote! {
                #[foo]
                #[baz]
                #[test]
                fn a() {}
            }
        )
    }

    #[test]
    fn already_exists_single() {
        let mut item_fn: syn::ItemFn = syn::parse_quote! {
            #[test]
            fn a() {}
        };
        attrs_add_test(&mut item_fn.attrs);
        assert_eq!(
            item_fn,
            syn::parse_quote! {
                #[test]
                fn a() {}
            }
        )
    }

    #[test]
    fn already_exists_multiple() {
        let mut item_fn: syn::ItemFn = syn::parse_quote! {
            #[bar]
            #[test]
            #[xuuq]
            fn a() {}
        };
        attrs_add_test(&mut item_fn.attrs);
        assert_eq!(
            item_fn,
            syn::parse_quote! {
                #[bar]
                #[test]
                #[xuuq]
                fn a() {}
            }
        )
    }
}

mod signature_clear {
    use super::signature_clear;

    #[test]
    fn minimal() {
        let mut item_fn: syn::ItemFn = syn::parse_quote! {
            fn baz() {}
        };
        signature_clear(&mut item_fn.sig);
        assert_eq!(
            item_fn,
            syn::parse_quote! {
                fn baz() {}
            }
        )
    }

    #[test]
    fn qualifiers() {
        let mut item_fn: syn::ItemFn = syn::parse_quote! {
            async unsafe fn baz() {}
        };
        signature_clear(&mut item_fn.sig);
        assert_eq!(
            item_fn,
            syn::parse_quote! {
                async unsafe fn baz() {}
            }
        )
    }

    #[test]
    fn generics() {
        let mut item_fn: syn::ItemFn = syn::parse_quote! {
            fn baz<A, B>() where A: Default {}
        };
        signature_clear(&mut item_fn.sig);
        assert_eq!(
            item_fn,
            syn::parse_quote! {
                fn baz<A, B>() where A: Default {}
            }
        )
    }

    #[test]
    fn args() {
        let mut item_fn: syn::ItemFn = syn::parse_quote! {
            fn baz(&self, a: u32) {}
        };
        signature_clear(&mut item_fn.sig);
        assert_eq!(
            item_fn,
            syn::parse_quote! {
                fn baz() {}
            }
        )
    }

    #[test]
    fn return_type() {
        let mut item_fn: syn::ItemFn = syn::parse_quote! {
            fn baz() -> io::Result<()> {}
        };
        signature_clear(&mut item_fn.sig);
        assert_eq!(
            item_fn,
            syn::parse_quote! {
                fn baz() {}
            }
        )
    }

    #[test]
    fn full() {
        let mut item_fn: syn::ItemFn = syn::parse_quote! {
            const async unsafe extern "C" fn baz<T, U>(
                &mut self,
                x: usize,
                other: &Self,
                y: Box<String>
            ) -> bool
            where U: Debug + ToString
            {
                println!("quux");
            }
        };
        signature_clear(&mut item_fn.sig);
        assert_eq!(
            item_fn,
            syn::parse_quote! {
                const async unsafe extern "C" fn baz<T, U>()
                where U: Debug + ToString
                {
                    println!("quux");
                }
            }
        )
    }
}

mod attr_args {
    use super::{util, AttrArgs};

    #[test]
    fn empty() {
        let attr_args = syn::parse2(quote::quote![]).map_err(util::Error::from);
        assert_eq!(
            attr_args,
            Ok(AttrArgs {
                config: syn::parse_quote![Default::default()]
            })
        );
    }

    #[test]
    fn config_struct() {
        let attr_args = syn::parse2(quote::quote![config = Config { a: 123 }])
            .map_err(util::Error::from);
        assert_eq!(
            attr_args,
            Ok(AttrArgs {
                config: syn::parse_quote![Config { a: 123 }],
            })
        );
    }

    #[test]
    fn config_block() {
        let attr_args = syn::parse2(quote::quote! {
            config = {
                let mut config = Config::new();
                config.a = 123;
                config
            }
        })
        .map_err(util::Error::from);
        assert_eq!(
            attr_args,
            Ok(AttrArgs {
                config: syn::parse_quote! {{
                    let mut config = Config::new();
                    config.a = 123;
                    config
                }},
            })
        );
    }

    #[test]
    fn terminating_comma() {
        let attr_args = syn::parse2(quote::quote! {
            config = Config { a: 123 },
        })
        .map_err(util::Error::from);
        assert_eq!(
            attr_args,
            Ok(AttrArgs {
                config: syn::parse_quote![Config { a: 123 }],
            })
        );
    }

    #[test]
    fn config_multiple() {
        let attr_args: Result<AttrArgs, _> = syn::parse2(quote::quote![
            config = Config { a: 123 },
            config = Config { b: 456 }
        ])
        .map_err(Into::into);
        assert_eq!(
            attr_args,
            Err(util::Error::new("multiple instances of attribute argument",))
        );
    }

    #[test]
    fn illegal_argument() {
        let attr_args: Result<AttrArgs, _> = syn::parse2(quote::quote![
            config = Config { a: 123 },
            foo_bar = "quux"
        ])
        .map_err(Into::into);
        assert_eq!(
            attr_args,
            Err(util::Error::new("illegal attribute argument",))
        );
    }

    #[test]
    fn invalid_format() {
        let attr_args: Result<AttrArgs, _> =
            syn::parse2(quote::quote![Config { a: 123 }]);
        assert!(attr_args.is_err());
    }
}

mod util {
    use super::*;

    #[allow(dead_code)]
    pub fn proptest_impl(
        attr: TokenStream,
        item: TokenStream,
    ) -> Result<TokenStream, Error> {
        super::proptest_impl(attr.0, item.0)
            .map(TokenStream)
            .map_err(Error)
    }

    pub struct TokenStream(pm2::TokenStream);

    impl fmt::Debug for TokenStream {
        fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
            fmt::Display::fmt(&self.0, f)
        }
    }

    impl From<pm2::TokenStream> for TokenStream {
        fn from(stream: pm2::TokenStream) -> Self {
            Self(stream)
        }
    }

    impl PartialEq for TokenStream {
        fn eq(&self, other: &Self) -> bool {
            let trees_this = self.0.clone().into_iter().map(TokenTree);
            let trees_that = other.0.clone().into_iter().map(TokenTree);
            trees_this.eq(trees_that)
        }
    }

    struct TokenTree(pm2::TokenTree);

    impl PartialEq for TokenTree {
        fn eq(&self, other: &Self) -> bool {
            use pm2::TokenTree as TT;
            match &self.0 {
                TT::Group(this) => match &other.0 {
                    TT::Group(that) => {
                        Group(this.clone()) == Group(that.clone())
                    }
                    _ => false,
                },
                TT::Ident(this) => match &other.0 {
                    TT::Ident(that) => *this == *that,
                    _ => false,
                },
                TT::Punct(this) => match &other.0 {
                    TT::Punct(that) => {
                        Punct(this.clone()) == Punct(that.clone())
                    }
                    _ => false,
                },
                TT::Literal(this) => match &other.0 {
                    TT::Literal(that) => {
                        Literal(this.clone()) == Literal(that.clone())
                    }
                    _ => false,
                },
            }
        }
    }

    struct Group(pm2::Group);

    impl PartialEq for Group {
        fn eq(&self, other: &Self) -> bool {
            self.0.delimiter() == other.0.delimiter()
                && TokenStream(self.0.stream()) == TokenStream(other.0.stream())
        }
    }

    struct Punct(pm2::Punct);

    impl PartialEq for Punct {
        fn eq(&self, other: &Self) -> bool {
            self.0.as_char() == other.0.as_char()
                && self.0.spacing() == other.0.spacing()
        }
    }

    struct Literal(pm2::Literal);

    impl PartialEq for Literal {
        fn eq(&self, other: &Self) -> bool {
            self.0.to_string() == other.0.to_string()
        }
    }

    pub struct Error(syn::Error);

    impl Error {
        pub fn new<T>(message: T) -> Self
        where
            T: fmt::Display,
        {
            Self(syn::Error::new(pm2::Span::call_site(), message))
        }
    }

    impl fmt::Debug for Error {
        fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
            fmt::Display::fmt(&self.0.to_compile_error(), f)
        }
    }

    impl From<syn::Error> for Error {
        fn from(error: syn::Error) -> Self {
            Self(error)
        }
    }

    impl PartialEq for Error {
        fn eq(&self, other: &Self) -> bool {
            TokenStream(self.0.to_compile_error())
                == TokenStream(other.0.to_compile_error())
        }
    }
}
