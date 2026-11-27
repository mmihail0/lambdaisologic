use crate::eval::normalize;
use crate::syntax::{Term, Type};
use crate::typecheck::{check, Context};

pub const DEFAULT_SEARCH_DEPTH: usize = 32;

#[derive(Clone)]
struct Hyp {
    term: Term,
    ty: Type,
}

fn fresh_name(counter: &mut usize, prefix: &str) -> String {
    let name = format!("{}{}", prefix, *counter);
    *counter += 1;
    name
}

fn strip_lam_annotations(term: &Term) -> Term {
    match term {
        Term::Var(_) | Term::Unit => term.clone(),
        Term::Lam { param, body, .. } => Term::lam(param.clone(), None, strip_lam_annotations(body)),
        Term::App(f, a) => Term::app(strip_lam_annotations(f), strip_lam_annotations(a)),
        Term::Pair(l, r) => Term::pair(strip_lam_annotations(l), strip_lam_annotations(r)),
        Term::Fst(e) => Term::fst(strip_lam_annotations(e)),
        Term::Snd(e) => Term::snd(strip_lam_annotations(e)),
        Term::Inl(e) => Term::inl(strip_lam_annotations(e)),
        Term::Inr(e) => Term::inr(strip_lam_annotations(e)),
        Term::Case {
            scrutinee,
            left_var,
            left_body,
            right_var,
            right_body,
        } => Term::Case {
            scrutinee: Box::new(strip_lam_annotations(scrutinee)),
            left_var: left_var.clone(),
            left_body: Box::new(strip_lam_annotations(left_body)),
            right_var: right_var.clone(),
            right_body: Box::new(strip_lam_annotations(right_body)),
        },
        Term::Absurd(e, ty) => Term::absurd(strip_lam_annotations(e), ty.clone()),
        Term::Ann(e, ty) => Term::ann(strip_lam_annotations(e), ty.clone()),
        Term::CallCC { param, body, .. } => {
            Term::callcc(param.clone(), None, strip_lam_annotations(body))
        }
        Term::Throw {
            cont,
            value,
            target_ty,
        } => Term::throw(
            strip_lam_annotations(cont),
            strip_lam_annotations(value),
            target_ty.clone(),
        ),
    }
}

fn immediate_proof(hyps: &[Hyp], goal: &Type) -> Option<Term> {
    if *goal == Type::Top {
        return Some(Term::Unit);
    }
    if let Some(bot_hyp) = hyps.iter().find(|h| h.ty == Type::Bot) {
        return Some(if *goal == Type::Bot {
            bot_hyp.term.clone()
        } else {
            Term::absurd(bot_hyp.term.clone(), None)
        });
    }
    if let Some(match_hyp) = hyps.iter().find(|h| &h.ty == goal) {
        return Some(match_hyp.term.clone());
    }
    None
}

fn reduce_left_invertible(
    hyps: &mut Vec<Hyp>,
    goal: &Type,
    counter: &mut usize,
) -> Option<Term> {
    loop {
        if let Some(proof) = immediate_proof(hyps, goal) {
            return Some(proof);
        }
        let mut changed = false;
        for i in 0..hyps.len() {
            match &hyps[i].ty {
                Type::Top => {
                    hyps.remove(i);
                    changed = true;
                    break;
                }
                Type::Prod(_, _) => {
                    let hyp = hyps.remove(i);
                    if let Type::Prod(a, b) = hyp.ty {
                        hyps.push(Hyp {
                            term: Term::fst(hyp.term.clone()),
                            ty: *a,
                        });
                        hyps.push(Hyp {
                            term: Term::snd(hyp.term),
                            ty: *b,
                        });
                    }
                    changed = true;
                    break;
                }
                Type::Arrow(p, _) if **p == Type::Top => {
                    let hyp = hyps.remove(i);
                    if let Type::Arrow(_, q) = hyp.ty {
                        hyps.push(Hyp {
                            term: Term::app(hyp.term, Term::Unit),
                            ty: *q,
                        });
                    }
                    changed = true;
                    break;
                }
                Type::Arrow(p, _) if **p == Type::Bot => {
                    hyps.remove(i);
                    changed = true;
                    break;
                }
                Type::Arrow(p, _) if matches!(p.as_ref(), Type::Prod(_, _)) => {
                    let hyp = hyps.remove(i);
                    if let Type::Arrow(p_box, q) = hyp.ty {
                        if let Type::Prod(c, d) = *p_box {
                            let xc = fresh_name(counter, "x");
                            let xd = fresh_name(counter, "x");
                            let pair_term = Term::pair(Term::var(&xc), Term::var(&xd));
                            let curried = Term::lam(
                                xc,
                                Some((*c).clone()),
                                Term::lam(
                                    xd,
                                    Some((*d).clone()),
                                    Term::app(hyp.term, pair_term),
                                ),
                            );
                            hyps.push(Hyp {
                                term: curried,
                                ty: Type::Arrow(c, Box::new(Type::Arrow(d, q))),
                            });
                        }
                    }
                    changed = true;
                    break;
                }
                Type::Arrow(p, _) if matches!(p.as_ref(), Type::Sum(_, _)) => {
                    let hyp = hyps.remove(i);
                    if let Type::Arrow(p_box, q) = hyp.ty {
                        if let Type::Sum(c, d) = *p_box {
                            let xc = fresh_name(counter, "x");
                            let xd = fresh_name(counter, "x");
                            let left_fn = Term::lam(
                                xc.clone(),
                                Some((*c).clone()),
                                Term::app(hyp.term.clone(), Term::inl(Term::var(xc))),
                            );
                            let right_fn = Term::lam(
                                xd.clone(),
                                Some((*d).clone()),
                                Term::app(hyp.term, Term::inr(Term::var(xd))),
                            );
                            hyps.push(Hyp {
                                term: left_fn,
                                ty: Type::Arrow(c, q.clone()),
                            });
                            hyps.push(Hyp {
                                term: right_fn,
                                ty: Type::Arrow(d, q),
                            });
                        }
                    }
                    changed = true;
                    break;
                }
                Type::Arrow(p, _) if matches!(p.as_ref(), Type::Atom(_)) => {
                    let atom_match = hyps
                        .iter()
                        .enumerate()
                        .find(|(j, h)| *j != i && h.ty == **p)
                        .map(|(_, h)| h.term.clone());
                    if let Some(arg_term) = atom_match {
                        let hyp = hyps.remove(i);
                        if let Type::Arrow(_, q) = hyp.ty {
                            hyps.push(Hyp {
                                term: Term::app(hyp.term, arg_term),
                                ty: *q,
                            });
                        }
                        changed = true;
                        break;
                    }
                }
                _ => {}
            }
        }
        if !changed {
            return None;
        }
    }
}

fn search_sequent(
    mut hyps: Vec<Hyp>,
    goal: &Type,
    depth: usize,
    counter: &mut usize,
) -> Option<Term> {
    if let Some(proof) = immediate_proof(&hyps, goal) {
        return Some(proof);
    }
    if depth == 0 {
        return None;
    }

    match goal {
        Type::Arrow(a, b) => {
            let x = fresh_name(counter, "x");
            hyps.push(Hyp {
                term: Term::var(&x),
                ty: (**a).clone(),
            });
            let body = search_sequent(hyps, b, depth - 1, counter)?;
            return Some(Term::lam(x, Some((**a).clone()), body));
        }
        Type::Prod(a, b) => {
            let left = search_sequent(hyps.clone(), a, depth - 1, counter)?;
            let right = search_sequent(hyps, b, depth - 1, counter)?;
            return Some(Term::pair(left, right));
        }
        _ => {}
    }

    if let Some(proof) = reduce_left_invertible(&mut hyps, goal, counter) {
        return Some(proof);
    }

    if let Some(sum_idx) = hyps.iter().position(|h| matches!(h.ty, Type::Sum(_, _))) {
        let sum_hyp = hyps.remove(sum_idx);
        if let Type::Sum(a, b) = sum_hyp.ty {
            let xl = fresh_name(counter, "x");
            let mut left_hyps = hyps.clone();
            left_hyps.push(Hyp {
                term: Term::var(&xl),
                ty: *a,
            });
            let left_body = search_sequent(left_hyps, goal, depth - 1, counter)?;

            let xr = fresh_name(counter, "x");
            let mut right_hyps = hyps;
            right_hyps.push(Hyp {
                term: Term::var(&xr),
                ty: *b,
            });
            let right_body = search_sequent(right_hyps, goal, depth - 1, counter)?;

            return Some(Term::Case {
                scrutinee: Box::new(sum_hyp.term),
                left_var: xl,
                left_body: Box::new(left_body),
                right_var: xr,
                right_body: Box::new(right_body),
            });
        }
    }

    if let Type::Sum(a, b) = goal {
        if let Some(left_term) = search_sequent(hyps.clone(), a, depth - 1, counter) {
            return Some(Term::inl(left_term));
        }
        if let Some(right_term) = search_sequent(hyps.clone(), b, depth - 1, counter) {
            return Some(Term::inr(right_term));
        }
    }

    for i in 0..hyps.len() {
        if let Type::Arrow(p, q) = &hyps[i].ty {
            if let Type::Arrow(c, d) = p.as_ref() {
                let f = hyps[i].term.clone();
                let c_ty = (**c).clone();
                let d_ty = (**d).clone();
                let q_ty = (**q).clone();

                let mut rest = hyps.clone();
                rest.remove(i);

                let xc = fresh_name(counter, "x");
                let xd = fresh_name(counter, "x");
                let xu = fresh_name(counter, "x");
                let helper = Term::lam(
                    xd.clone(),
                    Some(d_ty.clone()),
                    Term::app(
                        f.clone(),
                        Term::lam(xu, Some(c_ty.clone()), Term::var(xd)),
                    ),
                );

                let mut sub_hyps = rest.clone();
                sub_hyps.push(Hyp {
                    term: Term::var(&xc),
                    ty: c_ty.clone(),
                });
                sub_hyps.push(Hyp {
                    term: helper,
                    ty: Type::arrow(d_ty.clone(), q_ty.clone()),
                });

                if let Some(body_d) = search_sequent(sub_hyps, &d_ty, depth - 1, counter) {
                    let arg_cd = Term::lam(xc, Some(c_ty), body_d);
                    let mut cont_hyps = rest;
                    cont_hyps.push(Hyp {
                        term: Term::app(f, arg_cd),
                        ty: q_ty,
                    });
                    if let Some(goal_term) = search_sequent(cont_hyps, goal, depth - 1, counter) {
                        return Some(goal_term);
                    }
                }
            }
        }
    }

    None
}

pub fn prove(goal: &Type, max_depth: usize) -> Option<Term> {
    let mut counter = 0usize;
    let raw = search_sequent(Vec::new(), goal, max_depth, &mut counter)?;
    let normalized = normalize(&raw);
    let stripped = strip_lam_annotations(&normalized);
    let empty = Context::new();
    if check(&empty, &stripped, goal).is_ok() {
        Some(stripped)
    } else if check(&empty, &normalized, goal).is_ok() {
        Some(normalized)
    } else {
        None
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::parser::parse_type;

    fn assert_provable(prop: &str) -> Term {
        let ty = parse_type(prop).unwrap();
        let term = prove(&ty, DEFAULT_SEARCH_DEPTH)
            .unwrap_or_else(|| panic!("expected '{}' to be provable", prop));
        check(&Context::new(), &term, &ty)
            .unwrap_or_else(|e| panic!("synthesized invalid term '{}' for '{}': {}", term, prop, e));
        term
    }

    fn assert_unprovable(prop: &str) {
        let ty = parse_type(prop).unwrap();
        assert!(
            prove(&ty, DEFAULT_SEARCH_DEPTH).is_none(),
            "expected '{}' to be unprovable in intuitionistic logic",
            prop
        );
    }

    #[test]
    fn proves_core_tautologies() {
        assert_provable("A -> A");
        assert_provable("A -> B -> A");
        assert_provable("(A -> B -> C) -> (A -> B) -> A -> C");
        assert_provable("A -> (A -> B) -> B");
        assert_provable("(A * B -> C) -> A -> B -> C");
        assert_provable("(A -> B -> C) -> A * B -> C");
        assert_provable("A * (B + C) -> (A * B) + (A * C)");
        assert_provable("(A * B) + (A * C) -> A * (B + C)");
        assert_provable("Bot -> A");
        assert_provable("A -> Top");
    }

    #[test]
    fn proves_constructive_demorgan_and_double_negation() {
        assert_provable("~(A + B) -> ~A * ~B");
        assert_provable("~A * ~B -> ~(A + B)");
        assert_provable("~A + ~B -> ~(A * B)");
        assert_provable("~~(A + ~A)");
        assert_provable("((A -> A) -> (B + C)) -> B + C");
    }

    #[test]
    fn rejects_non_constructive_propositions() {
        assert_unprovable("A + ~A");
        assert_unprovable("~~A -> A");
        assert_unprovable("((A -> B) -> A) -> A");
        assert_unprovable("~(A * B) -> ~A + ~B");
        assert_unprovable("A -> B");
    }

    #[test]
    fn respects_depth_bound() {
        let ty = parse_type("A -> B -> A").unwrap();
        assert!(prove(&ty, 0).is_none());
        assert!(prove(&ty, 1).is_none());
        assert!(prove(&ty, 2).is_some());
    }
}
