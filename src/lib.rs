extern crate proc_macro;

use darling::FromMeta;
use proc_macro::TokenStream;
use proc_macro2::Span;
use quote::quote;
use std::collections::HashMap;
use syn::{parse_macro_input, parse_quote, AttributeArgs, Expr, Ident, ItemFn, ReturnType, Type};

#[derive(Debug, FromMeta)]
struct MemoiseArgs {
    keys: HashMap<String, usize>,
}

#[proc_macro_attribute]
pub fn memoise(attr: TokenStream, item: TokenStream) -> TokenStream {
    let attr = parse_macro_input!(attr as AttributeArgs);
    let item_fn = parse_macro_input!(item as ItemFn);

    let args = MemoiseArgs::from_list(&attr).unwrap();
    let fn_sig = item_fn.sig;
    let fn_block = item_fn.block;

    let cache_ident = Ident::new(&fn_sig.ident.to_string().to_uppercase(), Span::call_site());
    let ret_type = if let ReturnType::Type(_, ty) = &fn_sig.output {
        ty
    } else {
        panic!("function return type is required");
    };

    let cache_type = (0..args.keys.len()).fold(
        parse_quote! { Option<#ret_type> },
        |acc: Type, _| parse_quote! { Vec<#acc> },
    );

    let cache_init = args
        .keys
        .values()
        .collect::<Vec<_>>()
        .into_iter()
        .rev()
        .fold(parse_quote! { None }, |acc: Type, len: &usize| {
            parse_quote! {
                vec![#acc; #len + 1]
            }
        });

    let key_vars = args
        .keys
        .keys()
        .map(|k| Ident::new(k, Span::call_site()))
        .collect::<Vec<_>>();

    let reset_expr = (0..args.keys.len()).fold(quote! { *r = None }, |acc, _| {
        quote! {
            for r in r.iter_mut() {
                #acc
            }
        }
    });

    let reset_expr: Expr = parse_quote! {
        {
            let mut r = cache.borrow_mut();
            #reset_expr;
        }
    };

    let reset_fn = Ident::new(
        &format!("{}_reset", fn_sig.ident.to_string()),
        Span::call_site(),
    );

    let gen = quote! {
        thread_local!(
            static #cache_ident: std::cell::RefCell<#cache_type> =
                std::cell::RefCell::new(#cache_init));

        fn #reset_fn() {
            #cache_ident.with(|cache| #reset_expr);
        }

        #fn_sig {
            if let Some(ret) = #cache_ident.with(|cache| cache.borrow()#([#key_vars])*) {
                return ret;
            }

            let ret: #ret_type = #fn_block;

            #cache_ident.with(|cache| {
                let mut bm = cache.borrow_mut();
                bm #([#key_vars])* = Some(ret);
            });

            ret
        }
    };

    gen.into()
}
