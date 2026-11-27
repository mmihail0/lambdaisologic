use std::collections::HashSet;

use crate::eval::normalize;
use crate::syntax::{Term, Type};
use crate::typecheck::{check, Context};

pub const DEFAULT_SEARCH_DEPTH: usize = 32;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum LogicMode {
    Intuitionistic,
    Classical,
}

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

fn strip_annotations(term: &Term) -> Term {
    match term {
        Term::Var(_) | Term::Unit => term.clone(),
        Term::Lam { param, body, .. } => Term::lam(param.clone(), None, strip_annotations(body)),
        Term::App(f, a) => Term::app(strip_annotations(f), strip_annotations(a)),
        Term::Pair(l, r) => Term::pair(strip_annotations(l), strip_annotations(r)),
        Term::Fst(e) => Term::fst(strip_annotations(e)),
        Term::Snd(e) => Term::snd(strip_annotations(e)),
        Term::Inl(e) => Term::inl(strip_annotations(e)),
        Term::Inr(e) => Term::inr(strip_annotations(e)),
        Term::Case {
            scrutinee,
            left_var,
            left_body,
            right_var,
            right_body,
        } => Term::Case {
            scrutinee: Box::new(strip_annotations(scrutinee)),
            left_var: left_var.clone(),
            left_body: Box::new(strip_annotations(left_body)),
            right_var: right_var.clone(),
            right_body: Box::new(strip_annotations(right_body)),
        },
        Term::Absurd(e, _) => Term::absurd(strip_annotations(e), None),
        Term::Ann(e, ty) => Term::ann(strip_annotations(e), ty.clone()),
        Term::CallCC { param, body, .. } => {
            Term::callcc(param.clone(), None, strip_annotations(body))
        }
        Term::Throw { cont, value, .. } => {
            Term::throw(strip_annotations(cont), strip_annotations(value), None)
        }
    }
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

fn free_vars(term: &Term) -> HashSet<String> {
    match term {
        Term::Var(name) => {
            let mut set = HashSet::new();
            set.insert(name.clone());
            set
        }
        Term::Unit => HashSet::new(),
        Term::Lam { param, body, .. } | Term::CallCC { param, body, .. } => {
            let mut set = free_vars(body);
            set.remove(param);
            set
        }
        Term::App(a, b) | Term::Pair(a, b) | Term::Throw { cont: a, value: b, .. } => {
            let mut set = free_vars(a);
            set.extend(free_vars(b));
            set
        }
        Term::Fst(inner)
        | Term::Snd(inner)
        | Term::Inl(inner)
        | Term::Inr(inner)
        | Term::Absurd(inner, _)
        | Term::Ann(inner, _) => free_vars(inner),
        Term::Case {
            scrutinee,
            left_var,
            left_body,
            right_var,
            right_body,
        } => {
            let mut set = free_vars(scrutinee);
            let mut lf = free_vars(left_body);
            lf.remove(left_var);
            let mut rf = free_vars(right_body);
            rf.remove(right_var);
            set.extend(lf);
            set.extend(rf);
            set
        }
    }
}

fn count_free_occurrences(term: &Term, var: &str) -> usize {
    match term {
        Term::Var(name) => usize::from(name == var),
        Term::Unit => 0,
        Term::Lam { param, body, .. } | Term::CallCC { param, body, .. } => {
            if param == var {
                0
            } else {
                count_free_occurrences(body, var)
            }
        }
        Term::App(a, b) | Term::Pair(a, b) | Term::Throw { cont: a, value: b, .. } => {
            count_free_occurrences(a, var) + count_free_occurrences(b, var)
        }
        Term::Fst(inner)
        | Term::Snd(inner)
        | Term::Inl(inner)
        | Term::Inr(inner)
        | Term::Absurd(inner, _)
        | Term::Ann(inner, _) => count_free_occurrences(inner, var),
        Term::Case {
            scrutinee,
            left_var,
            left_body,
            right_var,
            right_body,
        } => {
            let l = if left_var == var {
                0
            } else {
                count_free_occurrences(left_body, var)
            };
            let r = if right_var == var {
                0
            } else {
                count_free_occurrences(right_body, var)
            };
            count_free_occurrences(scrutinee, var) + l + r
        }
    }
}

fn fresh_alpha_var(base: &str, used: &HashSet<String>) -> String {
    let trimmed = base.trim_end_matches(|c: char| c.is_ascii_digit());
    let stem = if trimmed.is_empty() { base } else { trimmed };
    let mut idx = 1usize;
    loop {
        let candidate = format!("{}{}", stem, idx);
        if !used.contains(&candidate) {
            return candidate;
        }
        idx += 1;
    }
}

fn inline_subst_scoped(
    bound: &str,
    body: &Term,
    var: &str,
    replacement: &Term,
    rep_fv: &HashSet<String>,
) -> (String, Term) {
    let body_fv = free_vars(body);
    if bound == var || !body_fv.contains(var) {
        (bound.to_string(), body.clone())
    } else if rep_fv.contains(bound) {
        let mut avoid = rep_fv.clone();
        avoid.extend(body_fv);
        avoid.insert(var.to_string());
        let fresh = fresh_alpha_var(bound, &avoid);
        let renamed = inline_subst(body, bound, &Term::Var(fresh.clone()));
        (fresh, inline_subst(&renamed, var, replacement))
    } else {
        (bound.to_string(), inline_subst(body, var, replacement))
    }
}

fn inline_subst(term: &Term, var: &str, replacement: &Term) -> Term {
    match term {
        Term::Var(name) => {
            if name == var {
                replacement.clone()
            } else {
                term.clone()
            }
        }
        Term::Unit => Term::Unit,
        Term::Lam {
            param,
            param_ty,
            body,
        } => {
            let rep_fv = free_vars(replacement);
            let (new_param, new_body) = inline_subst_scoped(param, body, var, replacement, &rep_fv);
            Term::lam(new_param, param_ty.clone(), new_body)
        }
        Term::CallCC {
            param,
            param_ty,
            body,
        } => {
            let rep_fv = free_vars(replacement);
            let (new_param, new_body) = inline_subst_scoped(param, body, var, replacement, &rep_fv);
            Term::callcc(new_param, param_ty.clone(), new_body)
        }
        Term::App(f, a) => Term::app(
            inline_subst(f, var, replacement),
            inline_subst(a, var, replacement),
        ),
        Term::Pair(l, r) => Term::pair(
            inline_subst(l, var, replacement),
            inline_subst(r, var, replacement),
        ),
        Term::Fst(e) => Term::fst(inline_subst(e, var, replacement)),
        Term::Snd(e) => Term::snd(inline_subst(e, var, replacement)),
        Term::Inl(e) => Term::inl(inline_subst(e, var, replacement)),
        Term::Inr(e) => Term::inr(inline_subst(e, var, replacement)),
        Term::Absurd(e, ty) => Term::absurd(inline_subst(e, var, replacement), ty.clone()),
        Term::Ann(e, ty) => Term::ann(inline_subst(e, var, replacement), ty.clone()),
        Term::Throw {
            cont,
            value,
            target_ty,
        } => Term::throw(
            inline_subst(cont, var, replacement),
            inline_subst(value, var, replacement),
            target_ty.clone(),
        ),
        Term::Case {
            scrutinee,
            left_var,
            left_body,
            right_var,
            right_body,
        } => {
            let rep_fv = free_vars(replacement);
            let s = inline_subst(scrutinee, var, replacement);
            let (lv, lb) = inline_subst_scoped(left_var, left_body, var, replacement, &rep_fv);
            let (rv, rb) = inline_subst_scoped(right_var, right_body, var, replacement, &rep_fv);
            Term::Case {
                scrutinee: Box::new(s),
                left_var: lv,
                left_body: Box::new(lb),
                right_var: rv,
                right_body: Box::new(rb),
            }
        }
    }
}

fn is_simple_value(term: &Term) -> bool {
    match term {
        Term::Var(_) | Term::Unit => true,
        Term::Inl(e) | Term::Inr(e) => is_simple_value(e),
        Term::Pair(l, r) => is_simple_value(l) && is_simple_value(r),
        _ => false,
    }
}

fn simplify_proof(term: &Term) -> Term {
    match term {
        Term::Var(_) | Term::Unit => term.clone(),
        Term::Lam {
            param,
            param_ty,
            body,
        } => Term::lam(param.clone(), param_ty.clone(), simplify_proof(body)),
        Term::App(f, a) => {
            let sf = simplify_proof(f);
            let sa = simplify_proof(a);
            if let Term::Lam { param, body, .. } = &sf {
                if count_free_occurrences(body, param) <= 1 || is_simple_value(&sa) {
                    return simplify_proof(&inline_subst(body, param, &sa));
                }
            }
            Term::app(sf, sa)
        }
        Term::Pair(l, r) => Term::pair(simplify_proof(l), simplify_proof(r)),
        Term::Fst(e) => match simplify_proof(e) {
            Term::Pair(l, _) => *l,
            other => Term::fst(other),
        },
        Term::Snd(e) => match simplify_proof(e) {
            Term::Pair(_, r) => *r,
            other => Term::snd(other),
        },
        Term::Inl(e) => Term::inl(simplify_proof(e)),
        Term::Inr(e) => Term::inr(simplify_proof(e)),
        Term::Case {
            scrutinee,
            left_var,
            left_body,
            right_var,
            right_body,
        } => Term::Case {
            scrutinee: Box::new(simplify_proof(scrutinee)),
            left_var: left_var.clone(),
            left_body: Box::new(simplify_proof(left_body)),
            right_var: right_var.clone(),
            right_body: Box::new(simplify_proof(right_body)),
        },
        Term::Absurd(e, ty) => match simplify_proof(e) {
            Term::Throw { cont, value, .. } => Term::Throw {
                cont,
                value,
                target_ty: ty.clone(),
            },
            other => Term::absurd(other, ty.clone()),
        },
        Term::Ann(e, ty) => Term::ann(simplify_proof(e), ty.clone()),
        Term::CallCC {
            param,
            param_ty,
            body,
        } => {
            let simplified_body = match simplify_proof(body) {
                Term::Throw { cont, value, .. } if matches!(&*cont, Term::Var(k) if k == param) => {
                    *value
                }
                Term::Absurd(inner, _) => match *inner {
                    Term::Throw { cont, value, .. }
                        if matches!(&*cont, Term::Var(k) if k == param) =>
                    {
                        *value
                    }
                    other => Term::absurd(other, None),
                },
                other => other,
            };
            if !free_vars(&simplified_body).contains(param) {
                simplified_body
            } else {
                Term::callcc(param.clone(), param_ty.clone(), simplified_body)
            }
        }
        Term::Throw {
            cont,
            value,
            target_ty,
        } => Term::throw(
            simplify_proof(cont),
            simplify_proof(value),
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
                Type::Cont(_) => {
                    let hyp = hyps.remove(i);
                    if let Type::Cont(a) = hyp.ty {
                        let x = fresh_name(counter, "x");
                        let neg_fn = Term::lam(
                            x.clone(),
                            Some((*a).clone()),
                            Term::throw(hyp.term, Term::var(x), Some(Type::Bot)),
                        );
                        hyps.push(Hyp {
                            term: neg_fn,
                            ty: Type::arrow(*a, Type::Bot),
                        });
                    }
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

fn search_classical_sequent(
    mut hyps: Vec<Hyp>,
    goal: &Type,
    depth: usize,
    counter: &mut usize,
) -> Option<Term> {
    if let Some(proof) = search_sequent(hyps.clone(), goal, depth, counter) {
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
            let body = search_classical_sequent(hyps, b, depth - 1, counter)?;
            return Some(Term::lam(x, Some((**a).clone()), body));
        }
        Type::Prod(a, b) => {
            let left = search_classical_sequent(hyps.clone(), a, depth - 1, counter)?;
            let right = search_classical_sequent(hyps, b, depth - 1, counter)?;
            return Some(Term::pair(left, right));
        }
        _ => {}
    }

    let k = fresh_name(counter, "k");
    let x = fresh_name(counter, "x");
    let k_neg = Term::lam(
        x.clone(),
        Some(goal.clone()),
        Term::throw(Term::var(&k), Term::var(&x), Some(Type::Bot)),
    );
    hyps.push(Hyp {
        term: k_neg,
        ty: Type::not(goal.clone()),
    });
    let bot_term = search_sequent(hyps, &Type::Bot, depth - 1, counter)?;
    Some(Term::callcc(
        k,
        Some(Type::cont(goal.clone())),
        Term::absurd(bot_term, Some(goal.clone())),
    ))
}

pub fn prove(goal: &Type, max_depth: usize) -> Option<Term> {
    prove_with_mode(goal, max_depth, LogicMode::Intuitionistic)
}

pub fn prove_classical(goal: &Type, max_depth: usize) -> Option<Term> {
    prove_with_mode(goal, max_depth, LogicMode::Classical)
}

pub fn prove_with_mode(goal: &Type, max_depth: usize, mode: LogicMode) -> Option<Term> {
    let mut counter = 0usize;
    let raw = match mode {
        LogicMode::Intuitionistic => search_sequent(Vec::new(), goal, max_depth, &mut counter)?,
        LogicMode::Classical => {
            search_classical_sequent(Vec::new(), goal, max_depth, &mut counter)?
        }
    };
    let simplified = simplify_proof(&raw);
    let cleaned = match mode {
        LogicMode::Intuitionistic => normalize(&simplified),
        LogicMode::Classical => simplified,
    };
    let stripped = strip_annotations(&cleaned);
    let empty = Context::new();
    if check(&empty, &stripped, goal).is_ok() {
        Some(stripped)
    } else {
        let lam_stripped = strip_lam_annotations(&cleaned);
        if check(&empty, &lam_stripped, goal).is_ok() {
            Some(lam_stripped)
        } else if check(&empty, &cleaned, goal).is_ok() {
            Some(cleaned)
        } else {
            None
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::parser::parse_type;

    fn assert_provable_mode(prop: &str, mode: LogicMode) -> Term {
        let ty = parse_type(prop).unwrap();
        let term = prove_with_mode(&ty, DEFAULT_SEARCH_DEPTH, mode)
            .unwrap_or_else(|| panic!("expected '{}' to be provable in {:?}", prop, mode));
        check(&Context::new(), &term, &ty).unwrap_or_else(|e| {
            panic!("synthesized invalid term '{}' for '{}': {}", term, prop, e)
        });
        term
    }

    fn assert_unprovable_mode(prop: &str, mode: LogicMode) {
        let ty = parse_type(prop).unwrap();
        assert!(
            prove_with_mode(&ty, DEFAULT_SEARCH_DEPTH, mode).is_none(),
            "expected '{}' to be unprovable in {:?}",
            prop,
            mode
        );
    }

    #[test]
    fn proves_core_tautologies() {
        for prop in [
            "A -> A",
            "A -> B -> A",
            "(A -> B -> C) -> (A -> B) -> A -> C",
            "A -> (A -> B) -> B",
            "(A * B -> C) -> A -> B -> C",
            "(A -> B -> C) -> A * B -> C",
            "A * (B + C) -> (A * B) + (A * C)",
            "(A * B) + (A * C) -> A * (B + C)",
            "Bot -> A",
            "A -> Top",
            "Cont A -> Cont A",
            "Cont A -> ~A",
        ] {
            assert_provable_mode(prop, LogicMode::Intuitionistic);
        }
    }

    #[test]
    fn proves_constructive_demorgan_and_double_negation() {
        for prop in [
            "~(A + B) -> ~A * ~B",
            "~A * ~B -> ~(A + B)",
            "~A + ~B -> ~(A * B)",
            "~~(A + ~A)",
            "((A -> A) -> (B + C)) -> B + C",
        ] {
            assert_provable_mode(prop, LogicMode::Intuitionistic);
        }
    }

    #[test]
    fn rejects_non_constructive_propositions() {
        for prop in [
            "A + ~A",
            "~~A -> A",
            "((A -> B) -> A) -> A",
            "~(A * B) -> ~A + ~B",
            "A -> B",
        ] {
            assert_unprovable_mode(prop, LogicMode::Intuitionistic);
        }
    }

    #[test]
    fn proves_classical_tautologies_via_callcc() {
        for prop in [
            "((A -> B) -> A) -> A",
            "((A -> Void) -> Void) -> A",
            "Either A (A -> Void)",
            "((A * B) -> Void) -> Either (A -> Void) (B -> Void)",
            "(~A -> ~B) -> B -> A",
            "(A -> B) -> ~A + B",
            "(A -> B) + (B -> A)",
            "(~A -> A) -> A",
        ] {
            assert_provable_mode(prop, LogicMode::Classical);
        }

        for non_tautology in ["A -> B", "A + B", "(A -> B) -> B -> A"] {
            assert_unprovable_mode(non_tautology, LogicMode::Classical);
        }
    }

    #[test]
    fn respects_depth_bound() {
        let ty = parse_type("A -> B -> A").unwrap();
        assert!(prove(&ty, 0).is_none());
        assert!(prove(&ty, 1).is_none());
        assert!(prove(&ty, 2).is_some());
    }
}
