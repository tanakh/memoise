//! An attribute macro to memoise a function.
//!
//! # Usage
//!
//! You can just add attribute `memoise` to normal functions
//! that you want to memoise against arguments.
//! For example:
//!
//! ```
//! use memoise::memoise;
//!
//! #[memoise(n <= 100)]
//! fn fib(n: i64) -> i64 {
//!     if n == 0 || n == 1 {
//!         return n;
//!     }
//!     fib(n - 1) + fib(n - 2)
//! }
//! ```
//!
//! You need to specify upper-bound of arguments statically.
//! Bounds can be specified by `<` or `<=` and must be integer literal.
//! Calling memoised function by arguments that out of bounds
//! cause panic.
//!
//! You can specify multiple keys for memoise.
//!
//! ```
//! use memoise::memoise;
//!
//! #[memoise(n <= 100, m <= 50)]
//! fn comb(n: usize, m: usize) -> usize {
//!     if m == 0 {
//!         return 1;
//!     }
//!     if n == 0 {
//!         return 0;
//!     }
//!     comb(n - 1, m - 1) + comb(n - 1, m)
//! }
//! ```
//!
//! To reuse memoised functions depend on non-key arguments,
//! you can reset memoise tables by calling automatic defined
//! function named `<function-name>_reset`. On above code,
//! the function `comb_reset` is defined, so you can call
//! that function to reset the table.
//!
//! ```ignore
//! let a = comb(10, 5); // calculation
//! comb_reset();        // reset the memoization table
//! let a = comb(10, 5); // calculation executed again
//! ```
//!
//! You can also specify lower-bounds of keys.
//!
//! ```
//! use memoise::memoise;
//!
//! #[memoise(-100 <= n <= 100)]
//! fn foo(n: i64) -> i64 {
//!     todo!()
//! }
//! ```
//!
//! If lower-bounds are not specified,
//! concider '0 <= _' is specified implicitly.
//!
//! And you can specify keys as expressions instead of just variable names.
//!
//! ```
//! use memoise::memoise;
//!
//! #[memoise(n * 100 + m <= 100)]
//! fn bar(n: i64, m: i64) -> i64 {
//!     todo!()
//! }
//! ```
//!
//! Without bounds, cache table will be allocated dynamically.
//!
//! ```
//! use memoise::memoise;
//!
//! #[memoise(n, k)]
//! fn comb(n: usize, k: usize) -> usize {
//!     if k == 0 {
//!         return 1;
//!     }
//!     if n == 0 {
//!         return 0;
//!     }
//!     comb(n - 1, k - 1) + comb(n - 1, k)
//! }
//! ```
//!
//! `memoise_map` memoises a function with `BTreeMap`.
//!
//! ```
//! use memoise::memoise_map;
//!
//! #[memoise_map(n, k)]
//! fn comb(n: usize, k: usize) -> usize {
//!     if k == 0 {
//!         return 1;
//!     }
//!     if n == 0 {
//!         return 0;
//!     }
//!     comb(n - 1, k - 1) + comb(n - 1, k)
//! }
//! ```
//!

extern crate proc_macro;

use proc_macro::TokenStream;
use proc_macro2::Span;
use quote::quote;
use std::ops::Deref;
use syn::{
    parse::{Parse, ParseStream, Result},
    parse_macro_input, parse_quote, BinOp, Error, Expr, ExprBinary, ExprLit, ExprUnary, FnArg,
    Ident, ItemFn, Lit, LitInt, Pat, ReturnType, Token, Type,
};

#[derive(PartialEq, Eq, Debug)]
struct Key {
    expr: Expr,
    lower_bound: Option<(Expr, bool)>,
    upper_bound: Option<(Expr, bool)>,
}

impl Key {
    fn len(&self) -> Option<usize> {
        assert!(!(self.lower_bound.is_some() && self.upper_bound.is_none()));

        if let Some(ub) = &self.upper_bound {
            let lb = self.offset();

            let ub = (expr_to_i64(&ub.0), ub.1);
            let ub = ub.0 + if ub.1 { 1 } else { 0 };

            // range is [lb, ub)
            Some((ub - lb) as usize)
        } else {
            None
        }
    }

    fn offset(&self) -> i64 {
        let lb = self
            .lower_bound
            .as_ref()
            .map_or((0, true), |r| (expr_to_i64(&r.0), r.1));

        lb.0 + if lb.1 { 0 } else { 1 }
    }
}

// input must be `LitInt` or `- LitInt`
fn expr_to_i64(e: &Expr) -> i64 {
    match e {
        Expr::Unary(ExprUnary { expr, .. }) => -expr_to_i64(expr.deref()),
        Expr::Lit(ExprLit {
            lit: Lit::Int(n), ..
        }) => n.base10_parse().unwrap(),
        _ => unreachable!(),
    }
}

struct LitSignedInt(Expr);

impl Parse for LitSignedInt {
    fn parse(input: ParseStream) -> Result<Self> {
        let neg = if input.peek(Token![-]) {
            Some(input.parse::<Token![-]>()?)
        } else {
            None
        };
        let lit = input.parse::<LitInt>()?;

        let e = ExprLit {
            attrs: vec![],
            lit: lit.into(),
        }
        .into();

        Ok(LitSignedInt(if let Some(neg) = neg {
            ExprUnary {
                attrs: vec![],
                op: syn::UnOp::Neg(neg),
                expr: Box::new(e),
            }
            .into()
        } else {
            e
        }))
    }
}

#[test]
fn lit_signed_int_test() -> Result<()> {
    use syn::parse_str;

    assert_eq!(
        parse_str::<LitSignedInt>("100")?.0,
        parse_str::<Expr>("100")?
    );

    assert_eq!(
        parse_str::<LitSignedInt>("-100")?.0,
        parse_str::<Expr>("-100")?
    );

    assert!(parse_str::<LitSignedInt>("+100").is_err());
    assert!(parse_str::<LitSignedInt>("100 + 100").is_err());
    assert!(parse_str::<LitSignedInt>("100 < n").is_err());
    assert!(parse_str::<LitSignedInt>("100 <= n").is_err());
    assert!(parse_str::<LitSignedInt>("n < 100").is_err());
    assert!(parse_str::<LitSignedInt>("n <= 100").is_err());

    Ok(())
}

impl Parse for Key {
    fn parse(input: ParseStream) -> Result<Self> {
        let is_le = |op: &BinOp| match op {
            BinOp::Le(_) => true,
            _ => false,
        };

        let is_lt_or_le = |op: &BinOp| match op {
            BinOp::Lt(_) | BinOp::Le(_) => true,
            _ => false,
        };

        let is_lit_signed_int = |e: &Expr| match e {
            Expr::Lit(ExprLit { .. }) => true,
            Expr::Unary(ExprUnary { expr, .. }) => match expr.deref() {
                Expr::Lit(ExprLit { .. }) => true,
                _ => false,
            },
            _ => false,
        };

        let lower_bound = (|| -> Option<(Expr, bool)> {
            let ahead = input.fork();
            let _ = ahead.parse::<LitSignedInt>().ok()?;
            let op = ahead.parse::<BinOp>().ok()?;
            if is_lt_or_le(&op) {
                let b = input.parse::<LitSignedInt>().ok()?;
                let op = input.parse::<BinOp>().ok()?;
                Some((b.0, is_le(&op)))
            } else {
                None
            }
        })();

        let (expr, upper_bound) = match input.parse()? {
            Expr::Binary(ExprBinary {
                left, op, right, ..
            }) if is_lt_or_le(&op) => {
                if is_lit_signed_int(right.deref()) {
                    (*left, Some((*right, is_le(&op))))
                } else {
                    Err(Error::new(
                        Span::call_site(),
                        "upper_bound should be integer literal",
                    ))?
                }
            }

            e => (e, None),
        };

        Ok(Key {
            expr,
            lower_bound,
            upper_bound,
        })
    }
}

#[test]
fn parse_key_test() -> Result<()> {
    use syn::parse_str;

    assert_eq!(
        parse_str::<Key>("n")?,
        Key {
            expr: parse_str("n")?,
            lower_bound: None,
            upper_bound: None,
        }
    );

    assert_eq!(
        parse_str::<Key>("n < 100")?,
        Key {
            expr: parse_str("n")?,
            lower_bound: None,
            upper_bound: Some((parse_str("100")?, false)),
        }
    );

    assert_eq!(
        parse_str::<Key>("n <= 100")?,
        Key {
            expr: parse_str("n")?,
            lower_bound: None,
            upper_bound: Some((parse_str("100")?, true)),
        }
    );

    assert_eq!(
        parse_str::<Key>("-100 < n")?,
        Key {
            expr: parse_str("n")?,
            lower_bound: Some((parse_str("-100")?, false)),
            upper_bound: None,
        }
    );

    assert_eq!(
        parse_str::<Key>("0 <= n")?,
        Key {
            expr: parse_str("n")?,
            lower_bound: Some((parse_str("0")?, true)),
            upper_bound: None,
        }
    );

    assert_eq!(
        parse_str::<Key>("-100 < n < 100")?,
        Key {
            expr: parse_str("n")?,
            lower_bound: Some((parse_str("-100")?, false)),
            upper_bound: Some((parse_str("100")?, false)),
        }
    );

    assert_eq!(
        parse_str::<Key>("0 <= n < -100")?,
        Key {
            expr: parse_str("n")?,
            lower_bound: Some((parse_str("0")?, true)),
            upper_bound: Some((parse_str("-100")?, false)),
        }
    );

    assert_eq!(
        parse_str::<Key>("-100 < n <= 100")?,
        Key {
            expr: parse_str("n")?,
            lower_bound: Some((parse_str("-100")?, false)),
            upper_bound: Some((parse_str("100")?, true)),
        }
    );

    assert_eq!(
        parse_str::<Key>("-100 <= n <= 100")?,
        Key {
            expr: parse_str("n")?,
            lower_bound: Some((parse_str("-100")?, true)),
            upper_bound: Some((parse_str("100")?, true)),
        }
    );

    assert_eq!(
        parse_str::<Key>("-100 <= n + 100 <= 100")?,
        Key {
            expr: parse_str("n + 100")?,
            lower_bound: Some((parse_str("-100")?, true)),
            upper_bound: Some((parse_str("100")?, true)),
        }
    );

    assert_eq!(
        parse_str::<Key>("-100 <= 100 + n <= 100")?,
        Key {
            expr: parse_str("100 + n")?,
            lower_bound: Some((parse_str("-100")?, true)),
            upper_bound: Some((parse_str("100")?, true)),
        }
    );

    assert_eq!(
        parse_str::<Key>("0 <= (if n >= 0 { n * 2 } else { -n * 2 + 1 }) <= 100")?,
        Key {
            expr: parse_str("(if n >= 0 { n * 2 } else { -n * 2 + 1 })")?,
            lower_bound: Some((parse_str("0")?, true)),
            upper_bound: Some((parse_str("100")?, true)),
        }
    );

    assert!(parse_str::<Key>("n < n").is_err());
    assert!(parse_str::<Key>("n < n < n < n").is_err());

    // FIXME: make below exprs to fail
    // assert!(parse_str::<Key>("100 < 100").is_err());
    // assert!(parse_str::<Key>("n > n"));

    Ok(())
}

struct Keys(Vec<Key>);

impl Parse for Keys {
    fn parse(input: ParseStream) -> Result<Self> {
        Ok(Keys(
            input
                .parse_terminated::<Key, Token![,]>(Key::parse)?
                .into_iter()
                .collect::<Vec<Key>>(),
        ))
    }
}

#[test]
fn parse_keys_test() -> Result<()> {
    use syn::parse_str;

    assert_eq!(parse_str::<Keys>("n")?.0, vec![parse_str::<Key>("n")?]);

    assert_eq!(
        parse_str::<Keys>("n, m")?.0,
        vec![parse_str::<Key>("n")?, parse_str::<Key>("m")?]
    );

    assert_eq!(
        parse_str::<Keys>("n <= 100, m <= 50")?.0,
        vec![parse_str::<Key>("n <= 100")?, parse_str::<Key>("m <= 50")?]
    );

    assert_eq!(
        parse_str::<Keys>("50 <= n, m <= 50")?.0,
        vec![parse_str::<Key>("50 <= n")?, parse_str::<Key>("m <= 50")?]
    );

    Ok(())
}

/// Memoise function by using `Vec`
#[proc_macro_attribute]
pub fn memoise(attr: TokenStream, item: TokenStream) -> TokenStream {
    let keys = parse_macro_input!(attr as Keys).0;
    let item_fn = parse_macro_input!(item as ItemFn);

    let fn_sig = item_fn.sig;
    let fn_block = item_fn.block;

    let cache_ident = Ident::new(&fn_sig.ident.to_string().to_uppercase(), Span::call_site());
    let ret_type = if let ReturnType::Type(_, ty) = &fn_sig.output {
        ty
    } else {
        panic!("function return type is required");
    };

    let lengths = keys.iter().map(|r| r.len()).collect::<Vec<Option<usize>>>();

    let cache_type = lengths.iter().rev().fold(
        parse_quote! { Option<#ret_type> },
        |acc: Type, _| parse_quote! { Vec<#acc> },
    );

    let has_bounds: bool;

    let cache_init = if lengths.iter().all(|l| l.is_some()) {
        has_bounds = true;
        lengths
            .iter()
            .rev()
            .fold(parse_quote! { None }, |acc: Expr, limit| {
                parse_quote! {
                    vec![#acc; #limit]
                }
            })
    } else if lengths.iter().all(|l| l.is_none()) {
        has_bounds = false;
        parse_quote! {
            vec![]
        }
    } else {
        panic!("keys without bounds and keys with bounds are not allowed simultaneously")
    };

    let key_vars: Vec<Expr> = keys
        .iter()
        .map(|r| {
            let e = &r.expr;
            let ofs = r.offset();
            if ofs != 0 {
                parse_quote! { ((#e) as i64 - (#ofs)) as usize }
            } else {
                parse_quote! { (#e) as usize }
            }
        })
        .collect();

    let reset_expr: Expr = if has_bounds {
        (0..keys.len()).fold(parse_quote! { *r = None }, |acc, _| {
            parse_quote! {
                for r in r.iter_mut() {
                    #acc
                }
            }
        })
    } else {
        parse_quote! { r.clear() }
    };

    let cache_borrow_var: Ident = parse_quote! {bm};

    let alloc_expr = if has_bounds {
        quote! {}
    } else {
        let mut expr = quote! {};

        for i in 0..key_vars.len() {
            let ix = &key_vars[i];
            let ixs = &key_vars[0..i];
            let init_val: Expr = if i + 1 == key_vars.len() {
                parse_quote! { None }
            } else {
                parse_quote! { vec![] }
            };
            expr = quote! {
                #expr
                if #cache_borrow_var #([#ixs])*.len() <= #ix {
                    #cache_borrow_var #([#ixs])*.resize(#ix + 1, #init_val);
                }
            };
        }

        expr
    };

    let reset_expr: Expr = parse_quote! {
        {
            let mut r = cache.borrow_mut();
            #reset_expr;
        }
    };

    let reset_fn_name = Ident::new(
        &format!("{}_reset", fn_sig.ident.to_string()),
        Span::call_site(),
    );

    let gen = quote! {
        thread_local!(
            static #cache_ident: std::cell::RefCell<#cache_type> =
                std::cell::RefCell::new(#cache_init));

        fn #reset_fn_name() {
            #cache_ident.with(|cache| #reset_expr);
        }

        #fn_sig {
            if let Some(ret) = #cache_ident.with(|cache| {
                let mut #cache_borrow_var = cache.borrow_mut();
                #alloc_expr
                #cache_borrow_var#([#key_vars])*.clone()
            }) {
                return ret;
            }

            let ret: #ret_type = (|| #fn_block )();

            #cache_ident.with(|cache| {
                let mut #cache_borrow_var = cache.borrow_mut();
                #cache_borrow_var#([#key_vars])* = Some(ret.clone());
            });

            ret
        }
    };

    gen.into()
}

/// Memoise function by using `BTreeMap`
#[proc_macro_attribute]
pub fn memoise_map(attr: TokenStream, item: TokenStream) -> TokenStream {
    let keys = parse_macro_input!(attr as Keys).0;
    let item_fn = parse_macro_input!(item as ItemFn);

    for key in keys.iter() {
        assert!(
            key.lower_bound.is_none() && key.lower_bound.is_none(),
            "memoise_map does not allow to specify bounds of keys"
        );
    }

    let fn_sig = item_fn.sig;
    let fn_block = item_fn.block;

    let cache_ident = Ident::new(&fn_sig.ident.to_string().to_uppercase(), Span::call_site());
    let ret_type = if let ReturnType::Type(_, ty) = &fn_sig.output {
        ty
    } else {
        panic!("function return type is required");
    };

    let key_types: Vec<Type> = keys
        .iter()
        .map(|key| {
            fn_sig
                .inputs
                .iter()
                .find_map(|arg| {
                    let expr = &key.expr;
                    let pat: Pat = parse_quote! { #expr };
                    match arg {
                        FnArg::Typed(pat_type) if pat == *pat_type.pat => {
                            Some((*pat_type.ty).clone())
                        }
                        _ => None,
                    }
                })
                .expect(&format!("Cannot infer the type of key `{}`", {
                    let e = &key.expr;
                    quote!(#e).to_string()
                }))
        })
        .collect();

    let key_type: Type = parse_quote! { (#(#key_types),*) };

    let cache_type: Type = parse_quote! { std::collections::BTreeMap<#key_type, #ret_type> };

    let cache_init: Expr = parse_quote! {
        std::collections::BTreeMap::new()
    };

    let key_vars: Vec<Expr> = keys.iter().map(|r| r.expr.clone()).collect();

    let reset_expr: Expr = parse_quote! {
        {
            let mut r = cache.borrow_mut();
            r.clear();
        }
    };

    let reset_fn_name = Ident::new(
        &format!("{}_reset", fn_sig.ident.to_string()),
        Span::call_site(),
    );

    let gen = quote! {
        thread_local!(
            static #cache_ident: std::cell::RefCell<#cache_type> =
                std::cell::RefCell::new(#cache_init));

        fn #reset_fn_name() {
            #cache_ident.with(|cache| #reset_expr);
        }

        #fn_sig {
            if let Some(ret) = #cache_ident.with(|cache|
                cache.borrow().get(&(#(#key_vars),*)).cloned())
            {
                return ret.clone();
            }

            let ret: #ret_type = (|| #fn_block )();

            #cache_ident.with(|cache| {
                let mut bm = cache.borrow_mut();
                bm.insert((#(#key_vars),*), ret.clone());
            });

            ret
        }
    };

    gen.into()
}
