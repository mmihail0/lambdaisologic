use std::fmt;

use crate::syntax::{Declaration, Span, Term, Type};

#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct Context {
    bindings: Vec<(String, Type)>,
}

impl Context {
    pub fn new() -> Self {
        Self {
            bindings: Vec::new(),
        }
    }

    pub fn extend(&self, name: impl Into<String>, ty: Type) -> Self {
        let mut next = self.bindings.clone();
        next.push((name.into(), ty));
        Self { bindings: next }
    }

    pub fn lookup(&self, name: &str) -> Option<&Type> {
        self.bindings
            .iter()
            .rev()
            .find(|(n, _)| n == name)
            .map(|(_, ty)| ty)
    }

    pub fn len(&self) -> usize {
        self.bindings.len()
    }

    pub fn is_empty(&self) -> bool {
        self.bindings.is_empty()
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum TypeError {
    UnboundVariable {
        name: String,
    },
    TypeMismatch {
        expected: Type,
        found: Type,
        context: String,
    },
    AnnotationMismatch {
        param: String,
        expected: Type,
        annotated: Type,
    },
    ExpectedFunction {
        found: Type,
        term: Term,
    },
    ExpectedFunctionForLambda {
        expected: Type,
        term: Term,
    },
    ExpectedProduct {
        found: Type,
        term: Term,
    },
    ExpectedSum {
        found: Type,
        term: Term,
    },
    ExpectedContinuation {
        found: Type,
        term: Term,
    },
    BranchTypeMismatch {
        left: Type,
        right: Type,
    },
    CannotSynthesize {
        reason: String,
        term: Term,
    },
    CannotCheck {
        expected: Type,
        reason: String,
        term: Term,
    },
}

impl fmt::Display for TypeError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            TypeError::UnboundVariable { name } => write!(f, "unbound variable '{}'", name),
            TypeError::TypeMismatch {
                expected,
                found,
                context,
            } => write!(
                f,
                "type mismatch {}: expected {}, found {}",
                context, expected, found
            ),
            TypeError::AnnotationMismatch {
                param,
                expected,
                annotated,
            } => write!(
                f,
                "parameter '{}' annotation mismatch: expected {}, found {}",
                param, expected, annotated
            ),
            TypeError::ExpectedFunction { found, term } => write!(
                f,
                "expected function type for '{}', found {}",
                term, found
            ),
            TypeError::ExpectedFunctionForLambda { expected, term } => write!(
                f,
                "type mismatch for '{}': expected {}, found function abstraction",
                term, expected
            ),
            TypeError::ExpectedProduct { found, term } => {
                write!(f, "expected product type for '{}', found {}", term, found)
            }
            TypeError::ExpectedSum { found, term } => {
                write!(f, "expected sum type for '{}', found {}", term, found)
            }
            TypeError::ExpectedContinuation { found, term } => {
                write!(
                    f,
                    "expected continuation type for '{}', found {}",
                    term, found
                )
            }
            TypeError::BranchTypeMismatch { left, right } => write!(
                f,
                "case branch type mismatch: left branch has type {}, right branch has type {}",
                left, right
            ),
            TypeError::CannotSynthesize { reason, term } => {
                write!(f, "cannot synthesize type for '{}': {}", term, reason)
            }
            TypeError::CannotCheck {
                expected,
                reason,
                term,
            } => write!(
                f,
                "cannot check '{}' against expected type {}: {}",
                term, expected, reason
            ),
        }
    }
}

impl std::error::Error for TypeError {}

pub fn synthesize(ctx: &Context, term: &Term) -> Result<Type, TypeError> {
    match term {
        Term::Var(name) => ctx
            .lookup(name)
            .cloned()
            .ok_or_else(|| TypeError::UnboundVariable { name: name.clone() }),
        Term::Unit => Ok(Type::Top),
        Term::Ann(inner, ty) => {
            check(ctx, inner, ty)?;
            Ok(ty.clone())
        }
        Term::Lam {
            param,
            param_ty: Some(a),
            body,
        } => {
            let body_ty = synthesize(&ctx.extend(param.clone(), a.clone()), body)?;
            Ok(Type::arrow(a.clone(), body_ty))
        }
        Term::Lam { param_ty: None, .. } => Err(TypeError::CannotSynthesize {
            reason: "unannotated lambda requires an expected type".to_string(),
            term: term.clone(),
        }),
        Term::App(func, arg) => {
            let func_ty = synthesize(ctx, func)?;
            match func_ty {
                Type::Arrow(a, b) => {
                    check(ctx, arg, &a)?;
                    Ok(*b)
                }
                found => Err(TypeError::ExpectedFunction {
                    found,
                    term: (**func).clone(),
                }),
            }
        }
        Term::Pair(left, right) => {
            let lt = synthesize(ctx, left)?;
            let rt = synthesize(ctx, right)?;
            Ok(Type::prod(lt, rt))
        }
        Term::Fst(inner) => {
            let ty = synthesize(ctx, inner)?;
            match ty {
                Type::Prod(a, _) => Ok(*a),
                found => Err(TypeError::ExpectedProduct {
                    found,
                    term: (**inner).clone(),
                }),
            }
        }
        Term::Snd(inner) => {
            let ty = synthesize(ctx, inner)?;
            match ty {
                Type::Prod(_, b) => Ok(*b),
                found => Err(TypeError::ExpectedProduct {
                    found,
                    term: (**inner).clone(),
                }),
            }
        }
        Term::Inl(_) | Term::Inr(_) => Err(TypeError::CannotSynthesize {
            reason: "sum injection requires an expected sum type or annotation".to_string(),
            term: term.clone(),
        }),
        Term::Case {
            scrutinee,
            left_var,
            left_body,
            right_var,
            right_body,
        } => {
            let scrut_ty = synthesize(ctx, scrutinee)?;
            match scrut_ty {
                Type::Sum(a, b) => {
                    let lt = synthesize(&ctx.extend(left_var.clone(), *a), left_body)?;
                    let rt = synthesize(&ctx.extend(right_var.clone(), *b), right_body)?;
                    if lt == rt {
                        Ok(lt)
                    } else {
                        Err(TypeError::BranchTypeMismatch { left: lt, right: rt })
                    }
                }
                found => Err(TypeError::ExpectedSum {
                    found,
                    term: (**scrutinee).clone(),
                }),
            }
        }
        Term::Absurd(inner, Some(ty)) => {
            check(ctx, inner, &Type::Bot)?;
            Ok(ty.clone())
        }
        Term::Absurd(_, None) => Err(TypeError::CannotSynthesize {
            reason: "unannotated absurd requires an expected type".to_string(),
            term: term.clone(),
        }),
        Term::CallCC {
            param,
            param_ty: Some(Type::Cont(a)),
            body,
        } => {
            check(&ctx.extend(param.clone(), Type::cont((**a).clone())), body, a)?;
            Ok((**a).clone())
        }
        Term::CallCC {
            param_ty: Some(found),
            ..
        } => Err(TypeError::ExpectedContinuation {
            found: found.clone(),
            term: term.clone(),
        }),
        Term::CallCC { param_ty: None, .. } => Err(TypeError::CannotSynthesize {
            reason: "unannotated callcc requires an expected type or Cont annotation".to_string(),
            term: term.clone(),
        }),
        Term::Throw {
            cont,
            value,
            target_ty,
        } => {
            let cont_ty = synthesize(ctx, cont)?;
            match cont_ty {
                Type::Cont(a) => {
                    check(ctx, value, &a)?;
                    match target_ty {
                        Some(ty) => Ok(ty.clone()),
                        None => Err(TypeError::CannotSynthesize {
                            reason: "unannotated throw requires an expected type or type argument"
                                .to_string(),
                            term: term.clone(),
                        }),
                    }
                }
                found => Err(TypeError::ExpectedContinuation {
                    found,
                    term: (**cont).clone(),
                }),
            }
        }
    }
}

pub fn check(ctx: &Context, term: &Term, expected: &Type) -> Result<(), TypeError> {
    match term {
        Term::Lam {
            param,
            param_ty,
            body,
        } => match expected {
            Type::Arrow(a, b) => {
                if let Some(ann) = param_ty {
                    if ann != a.as_ref() {
                        return Err(TypeError::AnnotationMismatch {
                            param: param.clone(),
                            expected: (**a).clone(),
                            annotated: ann.clone(),
                        });
                    }
                }
                check(&ctx.extend(param.clone(), (**a).clone()), body, b)
            }
            other => Err(TypeError::ExpectedFunctionForLambda {
                expected: other.clone(),
                term: term.clone(),
            }),
        },
        Term::Pair(left, right) => match expected {
            Type::Prod(a, b) => {
                check(ctx, left, a)?;
                check(ctx, right, b)
            }
            other => match synthesize(ctx, term) {
                Ok(found) => Err(TypeError::TypeMismatch {
                    expected: other.clone(),
                    found,
                    context: format!("in pair '{}'", term),
                }),
                Err(_) => Err(TypeError::CannotCheck {
                    expected: other.clone(),
                    reason: "pair constructor requires a product type".to_string(),
                    term: term.clone(),
                }),
            },
        },
        Term::Inl(inner) => match expected {
            Type::Sum(a, _) => check(ctx, inner, a),
            other => Err(TypeError::CannotCheck {
                expected: other.clone(),
                reason: "left injection requires a sum type".to_string(),
                term: term.clone(),
            }),
        },
        Term::Inr(inner) => match expected {
            Type::Sum(_, b) => check(ctx, inner, b),
            other => Err(TypeError::CannotCheck {
                expected: other.clone(),
                reason: "right injection requires a sum type".to_string(),
                term: term.clone(),
            }),
        },
        Term::Case {
            scrutinee,
            left_var,
            left_body,
            right_var,
            right_body,
        } => {
            let scrut_ty = synthesize(ctx, scrutinee)?;
            match scrut_ty {
                Type::Sum(a, b) => {
                    check(&ctx.extend(left_var.clone(), *a), left_body, expected)?;
                    check(&ctx.extend(right_var.clone(), *b), right_body, expected)
                }
                found => Err(TypeError::ExpectedSum {
                    found,
                    term: (**scrutinee).clone(),
                }),
            }
        }
        Term::Absurd(inner, ann_ty) => {
            if let Some(ann) = ann_ty {
                if ann != expected {
                    return Err(TypeError::TypeMismatch {
                        expected: expected.clone(),
                        found: ann.clone(),
                        context: "in absurd type annotation".to_string(),
                    });
                }
            }
            check(ctx, inner, &Type::Bot)
        }
        Term::Unit => {
            if expected == &Type::Top {
                Ok(())
            } else {
                Err(TypeError::TypeMismatch {
                    expected: expected.clone(),
                    found: Type::Top,
                    context: "in unit value ()".to_string(),
                })
            }
        }
        Term::CallCC {
            param,
            param_ty,
            body,
        } => {
            let expected_cont = Type::cont(expected.clone());
            if let Some(ann) = param_ty {
                if ann != &expected_cont {
                    return Err(TypeError::AnnotationMismatch {
                        param: param.clone(),
                        expected: expected_cont,
                        annotated: ann.clone(),
                    });
                }
            }
            check(&ctx.extend(param.clone(), expected_cont), body, expected)
        }
        Term::Throw {
            cont,
            value,
            target_ty,
        } => {
            if let Some(ann) = target_ty {
                if ann != expected {
                    return Err(TypeError::TypeMismatch {
                        expected: expected.clone(),
                        found: ann.clone(),
                        context: "in throw type annotation".to_string(),
                    });
                }
            }
            let cont_ty = synthesize(ctx, cont)?;
            match cont_ty {
                Type::Cont(a) => check(ctx, value, &a),
                found => Err(TypeError::ExpectedContinuation {
                    found,
                    term: (**cont).clone(),
                }),
            }
        }
        _ => {
            let found = synthesize(ctx, term)?;
            if &found == expected {
                Ok(())
            } else {
                Err(TypeError::TypeMismatch {
                    expected: expected.clone(),
                    found,
                    context: format!("in term '{}'", term),
                })
            }
        }
    }
}

pub fn check_declaration(ctx: &Context, decl: &Declaration) -> Result<(), TypeError> {
    check(ctx, &decl.proof, &decl.ty)
}

pub fn check_program(decls: &[Declaration]) -> Result<Context, (String, Span, TypeError)> {
    let mut ctx = Context::new();
    for decl in decls {
        check_declaration(&ctx, decl).map_err(|e| (decl.name.clone(), decl.span, e))?;
        ctx = ctx.extend(decl.name.clone(), decl.ty.clone());
    }
    Ok(ctx)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::parser::{parse_program, parse_term, parse_type};

    #[test]
    fn valid_bidirectional_proofs() {
        let src = "
            theorem mp : A -> (A -> B) -> B = \\a f. f a
            theorem and_comm : A * B -> B * A = \\p. (snd p, fst p)
            theorem or_comm : A + B -> B + A = \\s. case s of inl x => inr x | inr y => inl y
            theorem absurd_elim : Bot -> A = \\e. absurd e
            theorem unit_intro : A -> Top = \\x. ()
        ";
        let decls = parse_program(src).unwrap();
        let ctx = check_program(&decls).unwrap();
        assert_eq!(ctx.len(), 5);
    }

    #[test]
    fn classical_continuation_proofs() {
        let src = "
            theorem peirce : ((A -> B) -> A) -> A =
              \\f. callcc (k : Cont A). f (\\a. throw k a)
            theorem dne : ((A -> Void) -> Void) -> A =
              \\dn. callcc k. absurd (dn (\\a. throw k a))
            theorem lem : Either A (A -> Void) =
              callcc k. inr (\\a. throw k (inl a))
            theorem classical_demorgan : ((A * B) -> Void) -> Either (A -> Void) (B -> Void) =
              \\nab. callcc k. inl (\\a. throw k (inr (\\b. nab (a, b))))
        ";
        let decls = parse_program(src).unwrap();
        let ctx = check_program(&decls).unwrap();
        assert_eq!(ctx.len(), 4);
    }

    #[test]
    fn synthesize_annotated_and_app() {
        let term = parse_term("\\(f : A -> B) (x : A). f x").unwrap();
        let ty = synthesize(&Context::new(), &term).unwrap();
        let expected = parse_type("(A -> B) -> A -> B").unwrap();
        assert_eq!(ty, expected);

        let cc = parse_term("callcc (k : Cont A). throw k a").unwrap();
        let ctx = Context::new().extend("a", Type::Atom("A".into()));
        assert_eq!(synthesize(&ctx, &cc).unwrap(), Type::Atom("A".into()));

        let th = parse_term("throw[B] k a").unwrap();
        let ctx2 = ctx.extend("k", Type::cont(Type::Atom("A".into())));
        assert_eq!(synthesize(&ctx2, &th).unwrap(), Type::Atom("B".into()));
    }

    #[test]
    fn lexical_shadowing_in_context() {
        let a = Type::Atom("A".into());
        let b = Type::Atom("B".into());
        let ctx = Context::new().extend("x", a).extend("x", b.clone());
        assert_eq!(ctx.lookup("x"), Some(&b));
    }

    #[test]
    fn invalid_type_mismatches() {
        let ty = parse_type("A * B -> A").unwrap();
        let bad_proj = parse_term("\\p. snd p").unwrap();
        let err = check(&Context::new(), &bad_proj, &ty).unwrap_err();
        assert!(matches!(
            err,
            TypeError::TypeMismatch {
                expected,
                found,
                ..
            } if expected == Type::Atom("A".into()) && found == Type::Atom("B".into())
        ));

        let bad_ann = parse_term("\\(p : B * A). fst p").unwrap();
        let err = check(&Context::new(), &bad_ann, &ty).unwrap_err();
        assert!(matches!(err, TypeError::AnnotationMismatch { .. }));

        let bad_absurd = parse_term("\\x. absurd x").unwrap();
        let ty_non_bot = parse_type("A -> B").unwrap();
        let err = check(&Context::new(), &bad_absurd, &ty_non_bot).unwrap_err();
        assert!(matches!(
            err,
            TypeError::TypeMismatch {
                expected: Type::Bot,
                ..
            }
        ));

        let bad_case = parse_term("\\(s : A + B). case s of inl x => x | inr y => y").unwrap();
        let err = synthesize(&Context::new(), &bad_case).unwrap_err();
        assert!(matches!(err, TypeError::BranchTypeMismatch { .. }));

        let unbound = parse_term("missing").unwrap();
        let err = synthesize(&Context::new(), &unbound).unwrap_err();
        assert!(matches!(err, TypeError::UnboundVariable { .. }));
    }

    #[test]
    fn continuation_type_errors() {
        let bad_cc_ann = parse_term("callcc (k : Cont B). throw k a").unwrap();
        let err = check(
            &Context::new().extend("a", Type::Atom("A".into())),
            &bad_cc_ann,
            &Type::Atom("A".into()),
        )
        .unwrap_err();
        assert!(matches!(err, TypeError::AnnotationMismatch { .. }));

        let bad_cc_non_cont = parse_term("callcc (k : A). k").unwrap();
        let err2 = synthesize(&Context::new(), &bad_cc_non_cont).unwrap_err();
        assert!(matches!(err2, TypeError::ExpectedContinuation { .. }));

        let bad_throw_target = parse_term("\\(x : A). throw x x").unwrap();
        let err3 = check(
            &Context::new(),
            &bad_throw_target,
            &parse_type("A -> B").unwrap(),
        )
        .unwrap_err();
        assert!(matches!(err3, TypeError::ExpectedContinuation { .. }));

        let bad_throw_payload = parse_term("callcc k. throw k ()").unwrap();
        let err4 = check(&Context::new(), &bad_throw_payload, &Type::Atom("A".into())).unwrap_err();
        assert!(matches!(
            err4,
            TypeError::TypeMismatch {
                expected,
                found: Type::Top,
                ..
            } if expected == Type::Atom("A".into())
        ));
    }
}
