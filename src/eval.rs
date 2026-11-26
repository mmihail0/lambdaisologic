use std::collections::HashSet;

use crate::syntax::Term;

pub fn free_vars(term: &Term) -> HashSet<String> {
    match term {
        Term::Var(name) => {
            let mut set = HashSet::new();
            set.insert(name.clone());
            set
        }
        Term::Unit => HashSet::new(),
        Term::Lam { param, body, .. } => {
            let mut set = free_vars(body);
            set.remove(param);
            set
        }
        Term::App(func, arg) | Term::Pair(func, arg) => {
            let mut set = free_vars(func);
            set.extend(free_vars(arg));
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
            let mut left_fv = free_vars(left_body);
            left_fv.remove(left_var);
            let mut right_fv = free_vars(right_body);
            right_fv.remove(right_var);
            set.extend(left_fv);
            set.extend(right_fv);
            set
        }
    }
}

fn fresh_var(base: &str, used: &HashSet<String>) -> String {
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

fn subst_branch(
    bound: &str,
    body: &Term,
    var: &str,
    replacement: &Term,
    rep_fv: &HashSet<String>,
) -> (String, Term) {
    if bound == var {
        (bound.to_string(), body.clone())
    } else if rep_fv.contains(bound) {
        let mut avoid = rep_fv.clone();
        avoid.extend(free_vars(body));
        avoid.insert(var.to_string());
        let fresh = fresh_var(bound, &avoid);
        let renamed = subst(body, bound, &Term::Var(fresh.clone()));
        (fresh, subst(&renamed, var, replacement))
    } else {
        (bound.to_string(), subst(body, var, replacement))
    }
}

pub fn subst(term: &Term, var: &str, replacement: &Term) -> Term {
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
            let (new_param, new_body) = subst_branch(param, body, var, replacement, &rep_fv);
            Term::lam(new_param, param_ty.clone(), new_body)
        }
        Term::App(func, arg) => Term::app(
            subst(func, var, replacement),
            subst(arg, var, replacement),
        ),
        Term::Pair(left, right) => Term::pair(
            subst(left, var, replacement),
            subst(right, var, replacement),
        ),
        Term::Fst(inner) => Term::fst(subst(inner, var, replacement)),
        Term::Snd(inner) => Term::snd(subst(inner, var, replacement)),
        Term::Inl(inner) => Term::inl(subst(inner, var, replacement)),
        Term::Inr(inner) => Term::inr(subst(inner, var, replacement)),
        Term::Case {
            scrutinee,
            left_var,
            left_body,
            right_var,
            right_body,
        } => {
            let rep_fv = free_vars(replacement);
            let new_scrutinee = subst(scrutinee, var, replacement);
            let (new_left_var, new_left_body) =
                subst_branch(left_var, left_body, var, replacement, &rep_fv);
            let (new_right_var, new_right_body) =
                subst_branch(right_var, right_body, var, replacement, &rep_fv);
            Term::Case {
                scrutinee: Box::new(new_scrutinee),
                left_var: new_left_var,
                left_body: Box::new(new_left_body),
                right_var: new_right_var,
                right_body: Box::new(new_right_body),
            }
        }
        Term::Absurd(inner, ty) => Term::absurd(subst(inner, var, replacement), ty.clone()),
        Term::Ann(inner, ty) => Term::ann(subst(inner, var, replacement), ty.clone()),
    }
}

pub fn whnf(term: &Term) -> Term {
    match term {
        Term::Ann(inner, _) => whnf(inner),
        Term::App(func, arg) => match whnf(func) {
            Term::Lam { param, body, .. } => whnf(&subst(&body, &param, arg)),
            other => Term::app(other, (**arg).clone()),
        },
        Term::Fst(inner) => match whnf(inner) {
            Term::Pair(left, _) => whnf(&left),
            other => Term::fst(other),
        },
        Term::Snd(inner) => match whnf(inner) {
            Term::Pair(_, right) => whnf(&right),
            other => Term::snd(other),
        },
        Term::Case {
            scrutinee,
            left_var,
            left_body,
            right_var,
            right_body,
        } => match whnf(scrutinee) {
            Term::Inl(val) => whnf(&subst(left_body, left_var, &val)),
            Term::Inr(val) => whnf(&subst(right_body, right_var, &val)),
            other => Term::Case {
                scrutinee: Box::new(other),
                left_var: left_var.clone(),
                left_body: left_body.clone(),
                right_var: right_var.clone(),
                right_body: right_body.clone(),
            },
        },
        _ => term.clone(),
    }
}

pub fn normalize(term: &Term) -> Term {
    match whnf(term) {
        t @ (Term::Var(_) | Term::Unit) => t,
        Term::Lam {
            param,
            param_ty,
            body,
        } => Term::lam(param, param_ty, normalize(&body)),
        Term::App(func, arg) => Term::app(normalize(&func), normalize(&arg)),
        Term::Pair(left, right) => Term::pair(normalize(&left), normalize(&right)),
        Term::Fst(inner) => Term::fst(normalize(&inner)),
        Term::Snd(inner) => Term::snd(normalize(&inner)),
        Term::Inl(inner) => Term::inl(normalize(&inner)),
        Term::Inr(inner) => Term::inr(normalize(&inner)),
        Term::Case {
            scrutinee,
            left_var,
            left_body,
            right_var,
            right_body,
        } => Term::Case {
            scrutinee: Box::new(normalize(&scrutinee)),
            left_var,
            left_body: Box::new(normalize(&left_body)),
            right_var,
            right_body: Box::new(normalize(&right_body)),
        },
        Term::Absurd(inner, ty) => Term::absurd(normalize(&inner), ty),
        Term::Ann(inner, _) => normalize(&inner),
    }
}

pub fn normalize_with_env(term: &Term, env: &[(String, Term)]) -> Term {
    let mut expanded = term.clone();
    for (name, def) in env.iter().rev() {
        expanded = subst(&expanded, name, def);
    }
    normalize(&expanded)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::parser::parse_term;

    #[test]
    fn beta_reduce_application_and_under_lambda() {
        let term = parse_term("\\z. (\\x y. x) z w").unwrap();
        let norm = normalize(&term);
        assert_eq!(norm.to_string(), "\\z. z");
    }

    #[test]
    fn capture_avoiding_substitution() {
        let term = parse_term("\\y. (\\x. \\y. x) y").unwrap();
        let norm = normalize(&term);
        assert_eq!(norm.to_string(), "\\y. \\y1. y");
    }

    #[test]
    fn reduce_pair_projections_and_case() {
        let p = parse_term("(fst (a, b), snd (a, b))").unwrap();
        assert_eq!(normalize(&p).to_string(), "(a, b)");

        let c1 = parse_term("case inl x of inl u => inr u | inr v => inl v").unwrap();
        assert_eq!(normalize(&c1).to_string(), "inr x");

        let c2 = parse_term("case inr y of inl u => inr u | inr v => inl v").unwrap();
        assert_eq!(normalize(&c2).to_string(), "inl y");
    }

    #[test]
    fn normalize_expands_env_safely() {
        let id = parse_term("\\x. x").unwrap();
        let term = parse_term("(\\id. id) (id a)").unwrap();
        let norm = normalize_with_env(&term, &[("id".to_string(), id)]);
        assert_eq!(norm.to_string(), "a");
    }
}
