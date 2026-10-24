use super::{BinOpKind, Expr, FieldExpr, Literal, PlaceExpr, Turbofish};
use crate::{
    grammar::{expr::IntegerValue, AdtId, Lt, Parameter, RefKind, ScalarId, ValueId},
    rust::FormalityLang as Rust,
};
use formality_core::{
    parse::{CoreParse, ParseError, ParseResult, Parser, Precedence, Scope},
    Set,
};
use std::{fmt::Debug, sync::Arc};

impl Debug for Literal {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{:?}_{:?}", self.value, self.ty)
    }
}

// Custom parsing for literals like `42_usize` || `42_i32`
// Let both `42_u32` and `42 _ u32` be accepted
impl CoreParse<Rust> for Literal {
    fn parse<'t>(scope: &Scope<Rust>, text: &'t str) -> ParseResult<'t, Self> {
        Parser::single_variant(scope, text, "Literal", |avt| {
            let text0 = avt.text();
            let re = regex::Regex::new("-?").expect("to be right");
            let is_negative = avt.regex_str(&re, "an optional minus sign").is_ok();

            let number: u128 = avt.number()?;
            avt.expect_char('_')?;

            avt.each_nonterminal(|ty: ScalarId, av| {
                if let ScalarId::Bool = ty {
                    return Err(ParseError::at(
                        av.text(),
                        "bool literal suffix are not allowed".to_string(),
                    ));
                }

                let value = if ty.is_signed() {
                    IntegerValue::Signed(try_into_i128(number, is_negative, text0)?)
                } else {
                    IntegerValue::Unsigned(try_into_u128(number, is_negative, text0)?)
                };

                av.ok(Literal {
                    value: value.clone(),
                    ty,
                })
            })
        })
    }
}

fn try_into_i128(
    number: u128,
    is_negative: bool,
    text0: &str,
) -> Result<i128, Set<ParseError<'_>>> {
    let max_plus_one = u128::try_from(i128::MAX).unwrap() + 1;

    // The value stored in `number` is the absolute value of the parsed number.  For example, in the
    // a-mir-formality program `-123 _ i128` the variable `number` contains the value 123, WITHOUT
    // the minus sign.
    //
    // Why is the special case for `(number == max_plus_one && is_negative == true)` required?  Consider the following VALID
    // expression `-170141183460469231731687303715884105728 _ i128`. The parser will store the
    // absolute number value of this expression in `number`.  Without the specical case, we would
    // try to convert the `u128` into an `i128` using
    // `i128::try_from(170141183460469231731687303715884105728)`, which will yield an error, because
    // the number is to big and does not fit into an i128.  However, the whole expression is valid!
    // Therefore, we explicitly match this case, where the absolute value is equal to 2^127 + 1 AND
    // has a minus sign.  If that is the case, we know, that the parser has original read the
    // smallest possible `i128` number.
    if number == max_plus_one && is_negative {
        Ok(i128::MIN)
    } else {
        i128::try_from(number)
            .or_else(|_| Err(ParseError::at(text0, "invalid i128".to_string())))
            .map(|n| if is_negative { n * -1 } else { n })
    }
}

fn try_into_u128(
    number: u128,
    is_negative: bool,
    text0: &str,
) -> Result<u128, Set<ParseError<'_>>> {
    if is_negative {
        return Err(ParseError::at(
            text0,
            "u128 can not be negative".to_string(),
        ));
    }
    Ok(number)
}

// The operator determines precedence, so the two BinOp cases are parsed
// separately while both produce the same Expr::BinOp representation.
impl CoreParse<Rust> for Expr {
    fn parse<'t>(scope: &Scope<Rust>, text: &'t str) -> ParseResult<'t, Self> {
        Parser::multi_variant(scope, text, "Expr", |parser| {
            parser.parse_variant("Expr::Assign", Precedence::right(0), |p| {
                p.each_nonterminal(|place: PlaceExpr, p| {
                    p.expect_char('=')?;
                    p.each_nonterminal(|expr: Arc<Expr>, p| {
                        p.ok(Expr::Assign {
                            place: place.clone(),
                            expr,
                        })
                    })
                })
            });

            parser.parse_variant("Expr::Call", Precedence::default(), |p| {
                p.each_nonterminal(|callee: Arc<Expr>, p| {
                    if matches!(&*callee, Expr::Assign { .. } | Expr::BinOp { .. }) {
                        return Err(ParseError::at(
                            p.text(),
                            "invalid function callee".to_string(),
                        ));
                    }
                    p.expect_char('(')?;
                    p.each_comma_nonterminal(|args: Vec<Expr>, p| {
                        p.expect_char(')')?;
                        p.ok(Expr::Call {
                            callee: callee.clone(),
                            args,
                        })
                    })
                })
            });

            parser.parse_variant_cast::<Literal>(Precedence::default());
            parser.parse_variant("Expr::True", Precedence::default(), |p| {
                p.expect_keyword("true")?;
                p.ok(Expr::True)
            });
            parser.parse_variant("Expr::False", Precedence::default(), |p| {
                p.expect_keyword("false")?;
                p.ok(Expr::False)
            });

            parser.parse_variant("Expr::Ref", Precedence::default(), |p| {
                p.expect_char('&')?;
                p.each_nonterminal(|lt: Lt, p| {
                    p.each_opt_nonterminal(|kind: Option<RefKind>, p| {
                        p.each_nonterminal(|place: PlaceExpr, p| {
                            p.ok(Expr::Ref {
                                kind: kind.clone().unwrap_or_default(),
                                lt: lt.clone(),
                                place,
                            })
                        })
                    })
                })
            });

            parser.parse_variant_cast::<PlaceExpr>(Precedence::default());
            parser.parse_variant("Expr::Turbofish", Precedence::default(), |p| {
                p.each_nonterminal(|id: ValueId, p| {
                    p.expect_char(':')?;
                    p.expect_char(':')?;
                    p.expect_char('<')?;
                    p.each_comma_nonterminal(|args: Vec<Parameter>, p| {
                        p.expect_char('>')?;
                        p.ok(Expr::Turbofish {
                            id: id.clone(),
                            args,
                        })
                    })
                })
            });

            parser.parse_variant("Expr::Struct", Precedence::default(), |p| {
                p.each_nonterminal(|adt_id: AdtId, p| {
                    p.each_opt_nonterminal(|turbofish: Option<Turbofish>, p| {
                        p.expect_char('{')?;
                        p.each_comma_nonterminal(|field_exprs: Vec<FieldExpr>, p| {
                            p.expect_char('}')?;
                            p.ok(Expr::Struct {
                                field_exprs,
                                adt_id: adt_id.clone(),
                                turbofish: turbofish.clone().unwrap_or_default(),
                            })
                        })
                    })
                })
            });

            for (op, level) in [(BinOpKind::Add, 1), (BinOpKind::Mul, 2)] {
                parser.parse_variant("Expr::BinOp", Precedence::left(level), |p| {
                    p.each_nonterminal(|lhs: Arc<Expr>, p| {
                        p.expect_char(match op {
                            BinOpKind::Add => '+',
                            BinOpKind::Mul => '*',
                        })?;
                        p.each_nonterminal(|rhs: Arc<Expr>, p| {
                            p.ok(Expr::BinOp {
                                lhs: lhs.clone(),
                                op: op.clone(),
                                rhs,
                            })
                        })
                    })
                });
            }
        })
    }
}
