use std::fmt;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Span {
    pub line: usize,
    pub col: usize,
}

impl Span {
    pub fn new(line: usize, col: usize) -> Self {
        Self { line, col }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Type {
    Atom(String),
    Arrow(Box<Type>, Box<Type>),
    Prod(Box<Type>, Box<Type>),
    Sum(Box<Type>, Box<Type>),
    Cont(Box<Type>),
    Top,
    Bot,
}

impl Type {
    pub fn arrow(from: Type, to: Type) -> Self {
        Self::Arrow(Box::new(from), Box::new(to))
    }

    pub fn prod(left: Type, right: Type) -> Self {
        Self::Prod(Box::new(left), Box::new(right))
    }

    pub fn sum(left: Type, right: Type) -> Self {
        Self::Sum(Box::new(left), Box::new(right))
    }

    pub fn cont(inner: Type) -> Self {
        Self::Cont(Box::new(inner))
    }

    pub fn not(inner: Type) -> Self {
        Self::arrow(inner, Self::Bot)
    }

    fn precedence(&self) -> u8 {
        match self {
            Type::Arrow(_, _) => 0,
            Type::Sum(_, _) => 1,
            Type::Prod(_, _) => 2,
            Type::Cont(_) => 3,
            Type::Atom(_) | Type::Top | Type::Bot => 4,
        }
    }

    fn fmt_with_prec(&self, f: &mut fmt::Formatter<'_>, min_prec: u8) -> fmt::Result {
        let prec = self.precedence();
        let needs_parens = prec < min_prec;
        if needs_parens {
            write!(f, "(")?;
        }
        match self {
            Type::Atom(name) => write!(f, "{}", name)?,
            Type::Top => write!(f, "Top")?,
            Type::Bot => write!(f, "Bot")?,
            Type::Arrow(from, to) => {
                from.fmt_with_prec(f, 1)?;
                write!(f, " -> ")?;
                to.fmt_with_prec(f, 0)?;
            }
            Type::Sum(left, right) => {
                left.fmt_with_prec(f, 1)?;
                write!(f, " + ")?;
                right.fmt_with_prec(f, 2)?;
            }
            Type::Prod(left, right) => {
                left.fmt_with_prec(f, 2)?;
                write!(f, " * ")?;
                right.fmt_with_prec(f, 3)?;
            }
            Type::Cont(inner) => {
                write!(f, "Cont ")?;
                inner.fmt_with_prec(f, 4)?;
            }
        }
        if needs_parens {
            write!(f, ")")?;
        }
        Ok(())
    }
}

impl fmt::Display for Type {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.fmt_with_prec(f, 0)
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Term {
    Var(String),
    Lam {
        param: String,
        param_ty: Option<Type>,
        body: Box<Term>,
    },
    App(Box<Term>, Box<Term>),
    Pair(Box<Term>, Box<Term>),
    Fst(Box<Term>),
    Snd(Box<Term>),
    Inl(Box<Term>),
    Inr(Box<Term>),
    Case {
        scrutinee: Box<Term>,
        left_var: String,
        left_body: Box<Term>,
        right_var: String,
        right_body: Box<Term>,
    },
    Unit,
    Absurd(Box<Term>, Option<Type>),
    Ann(Box<Term>, Type),
    CallCC {
        param: String,
        param_ty: Option<Type>,
        body: Box<Term>,
    },
    Throw {
        cont: Box<Term>,
        value: Box<Term>,
        target_ty: Option<Type>,
    },
}

impl Term {
    pub fn var(name: impl Into<String>) -> Self {
        Self::Var(name.into())
    }

    pub fn lam(param: impl Into<String>, param_ty: Option<Type>, body: Term) -> Self {
        Self::Lam {
            param: param.into(),
            param_ty,
            body: Box::new(body),
        }
    }

    pub fn app(func: Term, arg: Term) -> Self {
        Self::App(Box::new(func), Box::new(arg))
    }

    pub fn pair(left: Term, right: Term) -> Self {
        Self::Pair(Box::new(left), Box::new(right))
    }

    pub fn fst(inner: Term) -> Self {
        Self::Fst(Box::new(inner))
    }

    pub fn snd(inner: Term) -> Self {
        Self::Snd(Box::new(inner))
    }

    pub fn inl(inner: Term) -> Self {
        Self::Inl(Box::new(inner))
    }

    pub fn inr(inner: Term) -> Self {
        Self::Inr(Box::new(inner))
    }

    pub fn absurd(inner: Term, ty: Option<Type>) -> Self {
        Self::Absurd(Box::new(inner), ty)
    }

    pub fn ann(inner: Term, ty: Type) -> Self {
        Self::Ann(Box::new(inner), ty)
    }

    pub fn callcc(param: impl Into<String>, param_ty: Option<Type>, body: Term) -> Self {
        Self::CallCC {
            param: param.into(),
            param_ty,
            body: Box::new(body),
        }
    }

    pub fn throw(cont: Term, value: Term, target_ty: Option<Type>) -> Self {
        Self::Throw {
            cont: Box::new(cont),
            value: Box::new(value),
            target_ty,
        }
    }

    fn precedence(&self) -> u8 {
        match self {
            Term::Lam { .. } | Term::Case { .. } | Term::CallCC { .. } => 0,
            Term::App(_, _) => 1,
            Term::Fst(_)
            | Term::Snd(_)
            | Term::Inl(_)
            | Term::Inr(_)
            | Term::Absurd(_, _)
            | Term::Throw { .. } => 2,
            Term::Var(_) | Term::Pair(_, _) | Term::Unit | Term::Ann(_, _) => 3,
        }
    }

    fn fmt_with_prec(&self, f: &mut fmt::Formatter<'_>, min_prec: u8) -> fmt::Result {
        let prec = self.precedence();
        let needs_parens = prec < min_prec;
        if needs_parens {
            write!(f, "(")?;
        }
        match self {
            Term::Var(name) => write!(f, "{}", name)?,
            Term::Unit => write!(f, "()")?,
            Term::Lam {
                param,
                param_ty,
                body,
            } => {
                match param_ty {
                    Some(ty) => write!(f, "\\({} : {}). ", param, ty)?,
                    None => write!(f, "\\{}. ", param)?,
                }
                body.fmt_with_prec(f, 0)?;
            }
            Term::App(func, arg) => {
                func.fmt_with_prec(f, 1)?;
                write!(f, " ")?;
                arg.fmt_with_prec(f, 3)?;
            }
            Term::Pair(left, right) => {
                write!(f, "(")?;
                left.fmt_with_prec(f, 0)?;
                write!(f, ", ")?;
                right.fmt_with_prec(f, 0)?;
                write!(f, ")")?;
            }
            Term::Fst(inner) => {
                write!(f, "fst ")?;
                inner.fmt_with_prec(f, 3)?;
            }
            Term::Snd(inner) => {
                write!(f, "snd ")?;
                inner.fmt_with_prec(f, 3)?;
            }
            Term::Inl(inner) => {
                write!(f, "inl ")?;
                inner.fmt_with_prec(f, 3)?;
            }
            Term::Inr(inner) => {
                write!(f, "inr ")?;
                inner.fmt_with_prec(f, 3)?;
            }
            Term::Case {
                scrutinee,
                left_var,
                left_body,
                right_var,
                right_body,
            } => {
                write!(f, "case ")?;
                scrutinee.fmt_with_prec(f, 0)?;
                write!(f, " of inl {} => ", left_var)?;
                left_body.fmt_with_prec(f, 0)?;
                write!(f, " | inr {} => ", right_var)?;
                right_body.fmt_with_prec(f, 0)?;
            }
            Term::Absurd(inner, ty) => {
                match ty {
                    Some(t) => write!(f, "absurd[{}] ", t)?,
                    None => write!(f, "absurd ")?,
                }
                inner.fmt_with_prec(f, 3)?;
            }
            Term::Ann(inner, ty) => {
                write!(f, "(")?;
                inner.fmt_with_prec(f, 0)?;
                write!(f, " : {})", ty)?;
            }
            Term::CallCC {
                param,
                param_ty,
                body,
            } => {
                match param_ty {
                    Some(ty) => write!(f, "callcc ({} : {}). ", param, ty)?,
                    None => write!(f, "callcc {}. ", param)?,
                }
                body.fmt_with_prec(f, 0)?;
            }
            Term::Throw {
                cont,
                value,
                target_ty,
            } => {
                match target_ty {
                    Some(ty) => write!(f, "throw[{}] ", ty)?,
                    None => write!(f, "throw ")?,
                }
                cont.fmt_with_prec(f, 3)?;
                write!(f, " ")?;
                value.fmt_with_prec(f, 3)?;
            }
        }
        if needs_parens {
            write!(f, ")")?;
        }
        Ok(())
    }
}

impl fmt::Display for Term {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.fmt_with_prec(f, 0)
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Declaration {
    pub name: String,
    pub ty: Type,
    pub proof: Term,
    pub span: Span,
}

impl fmt::Display for Declaration {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "theorem {} : {} = {}", self.name, self.ty, self.proof)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn type_display_precedence() {
        let a = Type::Atom("A".to_string());
        let b = Type::Atom("B".to_string());
        let c = Type::Atom("C".to_string());

        let right_assoc = Type::arrow(a.clone(), Type::arrow(b.clone(), c.clone()));
        assert_eq!(right_assoc.to_string(), "A -> B -> C");

        let left_arrow = Type::arrow(Type::arrow(a.clone(), b.clone()), c.clone());
        assert_eq!(left_arrow.to_string(), "(A -> B) -> C");

        let mixed = Type::prod(Type::sum(a.clone(), b.clone()), c);
        assert_eq!(mixed.to_string(), "(A + B) * C");

        assert_eq!(Type::cont(a.clone()).to_string(), "Cont A");
        assert_eq!(
            Type::cont(Type::arrow(a.clone(), b.clone())).to_string(),
            "Cont (A -> B)"
        );
        assert_eq!(Type::cont(Type::cont(a.clone())).to_string(), "Cont (Cont A)");
        assert_eq!(Type::prod(Type::cont(a), b).to_string(), "Cont A * B");
    }

    #[test]
    fn term_display_precedence() {
        let app_left = Term::app(Term::app(Term::var("f"), Term::var("x")), Term::var("y"));
        assert_eq!(app_left.to_string(), "f x y");

        let app_right = Term::app(Term::var("f"), Term::app(Term::var("x"), Term::var("y")));
        assert_eq!(app_right.to_string(), "f (x y)");

        let lam = Term::lam(
            "x",
            Some(Type::Atom("A".to_string())),
            Term::inl(Term::var("x")),
        );
        assert_eq!(lam.to_string(), "\\(x : A). inl x");

        let cc = Term::callcc(
            "k",
            Some(Type::cont(Type::Atom("A".to_string()))),
            Term::throw(Term::var("k"), Term::var("x"), None),
        );
        assert_eq!(cc.to_string(), "callcc (k : Cont A). throw k x");

        let app_cc = Term::app(
            Term::var("f"),
            Term::callcc("k", None, Term::throw(Term::var("k"), Term::Unit, Some(Type::Bot))),
        );
        assert_eq!(app_cc.to_string(), "f (callcc k. throw[Bot] k ())");
    }
}
