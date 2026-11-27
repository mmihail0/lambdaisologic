use std::collections::HashSet;
use std::fmt;

use crate::syntax::{Term, Type};

const MAX_STEPS: usize = 1_000_000;

#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct Env {
    bindings: Vec<(String, Value)>,
}

impl Env {
    pub fn new() -> Self {
        Self {
            bindings: Vec::new(),
        }
    }

    pub fn extend(&self, name: impl Into<String>, value: Value) -> Self {
        let mut next = self.bindings.clone();
        next.push((name.into(), value));
        Self { bindings: next }
    }

    pub fn lookup(&self, name: &str) -> Option<&Value> {
        self.bindings
            .iter()
            .rev()
            .find(|(n, _)| n == name)
            .map(|(_, val)| val)
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Frame {
    AppArg {
        arg: Term,
        env: Env,
    },
    AppFn {
        func: Value,
    },
    PairRight {
        right: Term,
        env: Env,
    },
    PairLeft {
        left: Value,
    },
    Fst,
    Snd,
    Inl,
    Inr,
    Case {
        left_var: String,
        left_body: Term,
        right_var: String,
        right_body: Term,
        env: Env,
    },
    Absurd(Option<Type>),
    ThrowVal {
        value: Term,
        env: Env,
        target_ty: Option<Type>,
    },
    ThrowCont {
        cont: Value,
        target_ty: Option<Type>,
    },
}

#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct Kont {
    pub frames: Vec<Frame>,
}

impl Kont {
    pub fn new() -> Self {
        Self { frames: Vec::new() }
    }

    pub fn push(&mut self, frame: Frame) {
        self.frames.push(frame);
    }

    pub fn pop(&mut self) -> Option<Frame> {
        self.frames.pop()
    }

    pub fn is_empty(&self) -> bool {
        self.frames.is_empty()
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Neutral {
    Var(String),
    App(Box<Neutral>, Box<Value>),
    Fst(Box<Neutral>),
    Snd(Box<Neutral>),
    Case {
        scrutinee: Box<Neutral>,
        left_var: String,
        left_body: Term,
        right_var: String,
        right_body: Term,
        env: Env,
    },
    Absurd(Box<Neutral>, Option<Type>),
    Throw {
        cont: Box<Neutral>,
        value: Box<Value>,
        target_ty: Option<Type>,
    },
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Value {
    Unit,
    Closure {
        param: String,
        param_ty: Option<Type>,
        body: Term,
        env: Env,
    },
    Pair(Box<Value>, Box<Value>),
    Inl(Box<Value>),
    Inr(Box<Value>),
    Kont(Kont),
    Neutral(Neutral),
}

impl fmt::Display for Value {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", read_back(self))
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum EvalError {
    InvalidApplication(Value),
    InvalidProjection(Value),
    InvalidCaseScrutinee(Value),
    InvalidAbsurd(Value),
    InvalidContinuation(Value),
    StepLimitExceeded,
}

impl fmt::Display for EvalError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            EvalError::InvalidApplication(v) => write!(f, "cannot apply non-function value '{}'", v),
            EvalError::InvalidProjection(v) => write!(f, "cannot project non-pair value '{}'", v),
            EvalError::InvalidCaseScrutinee(v) => {
                write!(f, "cannot match non-sum value '{}' in case", v)
            }
            EvalError::InvalidAbsurd(v) => {
                write!(f, "cannot eliminate non-neutral value '{}' with absurd", v)
            }
            EvalError::InvalidContinuation(v) => {
                write!(f, "cannot throw to non-continuation value '{}'", v)
            }
            EvalError::StepLimitExceeded => write!(f, "evaluation step limit exceeded"),
        }
    }
}

impl std::error::Error for EvalError {}

enum Step {
    Eval {
        term: Term,
        env: Env,
        kont: Kont,
    },
    Apply {
        value: Value,
        kont: Kont,
    },
}

pub fn eval(term: &Term) -> Result<Value, EvalError> {
    eval_with_env(term, &Env::new())
}

pub fn eval_with_env(term: &Term, env: &Env) -> Result<Value, EvalError> {
    let mut state = Step::Eval {
        term: term.clone(),
        env: env.clone(),
        kont: Kont::new(),
    };
    let mut steps = 0usize;

    loop {
        if steps >= MAX_STEPS {
            return Err(EvalError::StepLimitExceeded);
        }
        steps += 1;

        state = match state {
            Step::Eval {
                term,
                env,
                mut kont,
            } => match term {
                Term::Var(name) => {
                    let value = env
                        .lookup(&name)
                        .cloned()
                        .unwrap_or_else(|| Value::Neutral(Neutral::Var(name)));
                    Step::Apply { value, kont }
                }
                Term::Unit => Step::Apply {
                    value: Value::Unit,
                    kont,
                },
                Term::Lam {
                    param,
                    param_ty,
                    body,
                } => Step::Apply {
                    value: Value::Closure {
                        param,
                        param_ty,
                        body: *body,
                        env,
                    },
                    kont,
                },
                Term::Ann(inner, _) => Step::Eval {
                    term: *inner,
                    env,
                    kont,
                },
                Term::App(func, arg) => {
                    kont.push(Frame::AppArg {
                        arg: *arg,
                        env: env.clone(),
                    });
                    Step::Eval {
                        term: *func,
                        env,
                        kont,
                    }
                }
                Term::Pair(left, right) => {
                    kont.push(Frame::PairRight {
                        right: *right,
                        env: env.clone(),
                    });
                    Step::Eval {
                        term: *left,
                        env,
                        kont,
                    }
                }
                Term::Fst(inner) => {
                    kont.push(Frame::Fst);
                    Step::Eval {
                        term: *inner,
                        env,
                        kont,
                    }
                }
                Term::Snd(inner) => {
                    kont.push(Frame::Snd);
                    Step::Eval {
                        term: *inner,
                        env,
                        kont,
                    }
                }
                Term::Inl(inner) => {
                    kont.push(Frame::Inl);
                    Step::Eval {
                        term: *inner,
                        env,
                        kont,
                    }
                }
                Term::Inr(inner) => {
                    kont.push(Frame::Inr);
                    Step::Eval {
                        term: *inner,
                        env,
                        kont,
                    }
                }
                Term::Case {
                    scrutinee,
                    left_var,
                    left_body,
                    right_var,
                    right_body,
                } => {
                    kont.push(Frame::Case {
                        left_var,
                        left_body: *left_body,
                        right_var,
                        right_body: *right_body,
                        env: env.clone(),
                    });
                    Step::Eval {
                        term: *scrutinee,
                        env,
                        kont,
                    }
                }
                Term::Absurd(inner, ty) => {
                    kont.push(Frame::Absurd(ty));
                    Step::Eval {
                        term: *inner,
                        env,
                        kont,
                    }
                }
                Term::CallCC { param, body, .. } => {
                    let captured = Value::Kont(kont.clone());
                    let ext = env.extend(param, captured);
                    Step::Eval {
                        term: *body,
                        env: ext,
                        kont,
                    }
                }
                Term::Throw {
                    cont,
                    value,
                    target_ty,
                } => {
                    kont.push(Frame::ThrowVal {
                        value: *value,
                        env: env.clone(),
                        target_ty,
                    });
                    Step::Eval {
                        term: *cont,
                        env,
                        kont,
                    }
                }
            },
            Step::Apply { value, mut kont } => {
                let Some(frame) = kont.pop() else {
                    return Ok(value);
                };
                match frame {
                    Frame::AppArg { arg, env } => {
                        kont.push(Frame::AppFn { func: value });
                        Step::Eval {
                            term: arg,
                            env,
                            kont,
                        }
                    }
                    Frame::AppFn { func } => match func {
                        Value::Closure {
                            param, body, env, ..
                        } => Step::Eval {
                            term: body,
                            env: env.extend(param, value),
                            kont,
                        },
                        Value::Neutral(n) => Step::Apply {
                            value: Value::Neutral(Neutral::App(Box::new(n), Box::new(value))),
                            kont,
                        },
                        other => return Err(EvalError::InvalidApplication(other)),
                    },
                    Frame::PairRight { right, env } => {
                        kont.push(Frame::PairLeft { left: value });
                        Step::Eval {
                            term: right,
                            env,
                            kont,
                        }
                    }
                    Frame::PairLeft { left } => Step::Apply {
                        value: Value::Pair(Box::new(left), Box::new(value)),
                        kont,
                    },
                    Frame::Fst => match value {
                        Value::Pair(left, _) => Step::Apply { value: *left, kont },
                        Value::Neutral(n) => Step::Apply {
                            value: Value::Neutral(Neutral::Fst(Box::new(n))),
                            kont,
                        },
                        other => return Err(EvalError::InvalidProjection(other)),
                    },
                    Frame::Snd => match value {
                        Value::Pair(_, right) => Step::Apply {
                            value: *right,
                            kont,
                        },
                        Value::Neutral(n) => Step::Apply {
                            value: Value::Neutral(Neutral::Snd(Box::new(n))),
                            kont,
                        },
                        other => return Err(EvalError::InvalidProjection(other)),
                    },
                    Frame::Inl => Step::Apply {
                        value: Value::Inl(Box::new(value)),
                        kont,
                    },
                    Frame::Inr => Step::Apply {
                        value: Value::Inr(Box::new(value)),
                        kont,
                    },
                    Frame::Case {
                        left_var,
                        left_body,
                        right_var,
                        right_body,
                        env,
                    } => match value {
                        Value::Inl(v) => Step::Eval {
                            term: left_body,
                            env: env.extend(left_var, *v),
                            kont,
                        },
                        Value::Inr(v) => Step::Eval {
                            term: right_body,
                            env: env.extend(right_var, *v),
                            kont,
                        },
                        Value::Neutral(n) => Step::Apply {
                            value: Value::Neutral(Neutral::Case {
                                scrutinee: Box::new(n),
                                left_var,
                                left_body,
                                right_var,
                                right_body,
                                env,
                            }),
                            kont,
                        },
                        other => return Err(EvalError::InvalidCaseScrutinee(other)),
                    },
                    Frame::Absurd(ty) => match value {
                        Value::Neutral(n) => Step::Apply {
                            value: Value::Neutral(Neutral::Absurd(Box::new(n), ty)),
                            kont,
                        },
                        other => return Err(EvalError::InvalidAbsurd(other)),
                    },
                    Frame::ThrowVal {
                        value: val_term,
                        env,
                        target_ty,
                    } => {
                        kont.push(Frame::ThrowCont {
                            cont: value,
                            target_ty,
                        });
                        Step::Eval {
                            term: val_term,
                            env,
                            kont,
                        }
                    }
                    Frame::ThrowCont { cont, target_ty } => match cont {
                        Value::Kont(captured_kont) => Step::Apply {
                            value,
                            kont: captured_kont,
                        },
                        Value::Neutral(n) => Step::Apply {
                            value: Value::Neutral(Neutral::Throw {
                                cont: Box::new(n),
                                value: Box::new(value),
                                target_ty,
                            }),
                            kont,
                        },
                        other => return Err(EvalError::InvalidContinuation(other)),
                    },
                }
            }
        };
    }
}

fn free_vars_term(term: &Term) -> HashSet<String> {
    match term {
        Term::Var(name) => {
            let mut set = HashSet::new();
            set.insert(name.clone());
            set
        }
        Term::Unit => HashSet::new(),
        Term::Lam { param, body, .. } | Term::CallCC { param, body, .. } => {
            let mut set = free_vars_term(body);
            set.remove(param);
            set
        }
        Term::App(a, b) | Term::Pair(a, b) | Term::Throw { cont: a, value: b, .. } => {
            let mut set = free_vars_term(a);
            set.extend(free_vars_term(b));
            set
        }
        Term::Fst(inner)
        | Term::Snd(inner)
        | Term::Inl(inner)
        | Term::Inr(inner)
        | Term::Absurd(inner, _)
        | Term::Ann(inner, _) => free_vars_term(inner),
        Term::Case {
            scrutinee,
            left_var,
            left_body,
            right_var,
            right_body,
        } => {
            let mut set = free_vars_term(scrutinee);
            let mut lf = free_vars_term(left_body);
            lf.remove(left_var);
            let mut rf = free_vars_term(right_body);
            rf.remove(right_var);
            set.extend(lf);
            set.extend(rf);
            set
        }
    }
}

fn has_control(term: &Term) -> bool {
    match term {
        Term::CallCC { .. } | Term::Throw { .. } => true,
        Term::Var(_) | Term::Unit => false,
        Term::Lam { body, .. }
        | Term::Fst(body)
        | Term::Snd(body)
        | Term::Inl(body)
        | Term::Inr(body)
        | Term::Absurd(body, _)
        | Term::Ann(body, _) => has_control(body),
        Term::App(a, b) | Term::Pair(a, b) => has_control(a) || has_control(b),
        Term::Case {
            scrutinee,
            left_body,
            right_body,
            ..
        } => has_control(scrutinee) || has_control(left_body) || has_control(right_body),
    }
}

fn neutral_contains_kont(neutral: &Neutral) -> bool {
    match neutral {
        Neutral::Var(_) => false,
        Neutral::App(n, v) | Neutral::Throw { cont: n, value: v, .. } => {
            neutral_contains_kont(n) || value_contains_kont(v)
        }
        Neutral::Fst(n) | Neutral::Snd(n) | Neutral::Absurd(n, _) => neutral_contains_kont(n),
        Neutral::Case {
            scrutinee,
            left_var,
            left_body,
            right_var,
            right_body,
            env,
        } => {
            neutral_contains_kont(scrutinee)
                || closure_is_effectful(left_var, left_body, env)
                || closure_is_effectful(right_var, right_body, env)
        }
    }
}

fn value_contains_kont(val: &Value) -> bool {
    match val {
        Value::Unit => false,
        Value::Kont(_) => true,
        Value::Pair(a, b) => value_contains_kont(a) || value_contains_kont(b),
        Value::Inl(v) | Value::Inr(v) => value_contains_kont(v),
        Value::Neutral(n) => neutral_contains_kont(n),
        Value::Closure {
            param, body, env, ..
        } => closure_is_effectful(param, body, env),
    }
}

fn closure_is_effectful(param: &str, body: &Term, env: &Env) -> bool {
    if has_control(body) {
        return true;
    }
    let mut fvs = free_vars_term(body);
    fvs.remove(param);
    fvs.iter()
        .any(|name| env.lookup(name).map_or(false, value_contains_kont))
}

fn collect_used_from_term_and_env(term: &Term, env: &Env, used: &mut HashSet<String>) {
    for fv in free_vars_term(term) {
        match env.lookup(&fv) {
            Some(v) => collect_used_from_value(v, used),
            None => {
                used.insert(fv);
            }
        }
    }
}

fn collect_used_from_neutral(neutral: &Neutral, used: &mut HashSet<String>) {
    match neutral {
        Neutral::Var(name) => {
            used.insert(name.clone());
        }
        Neutral::App(n, v) | Neutral::Throw { cont: n, value: v, .. } => {
            collect_used_from_neutral(n, used);
            collect_used_from_value(v, used);
        }
        Neutral::Fst(n) | Neutral::Snd(n) | Neutral::Absurd(n, _) => {
            collect_used_from_neutral(n, used);
        }
        Neutral::Case {
            scrutinee,
            left_var,
            left_body,
            right_var,
            right_body,
            env,
        } => {
            collect_used_from_neutral(scrutinee, used);
            for fv in free_vars_term(left_body) {
                if fv != *left_var {
                    match env.lookup(&fv) {
                        Some(v) => collect_used_from_value(v, used),
                        None => {
                            used.insert(fv);
                        }
                    }
                }
            }
            for fv in free_vars_term(right_body) {
                if fv != *right_var {
                    match env.lookup(&fv) {
                        Some(v) => collect_used_from_value(v, used),
                        None => {
                            used.insert(fv);
                        }
                    }
                }
            }
        }
    }
}

fn collect_used_from_frame(frame: &Frame, used: &mut HashSet<String>) {
    match frame {
        Frame::AppArg { arg, env }
        | Frame::PairRight { right: arg, env }
        | Frame::ThrowVal { value: arg, env, .. } => {
            collect_used_from_term_and_env(arg, env, used);
        }
        Frame::AppFn { func: v }
        | Frame::PairLeft { left: v }
        | Frame::ThrowCont { cont: v, .. } => {
            collect_used_from_value(v, used);
        }
        Frame::Fst | Frame::Snd | Frame::Inl | Frame::Inr | Frame::Absurd(_) => {}
        Frame::Case {
            left_var,
            left_body,
            right_var,
            right_body,
            env,
        } => {
            for fv in free_vars_term(left_body) {
                if fv != *left_var {
                    match env.lookup(&fv) {
                        Some(v) => collect_used_from_value(v, used),
                        None => {
                            used.insert(fv);
                        }
                    }
                }
            }
            for fv in free_vars_term(right_body) {
                if fv != *right_var {
                    match env.lookup(&fv) {
                        Some(v) => collect_used_from_value(v, used),
                        None => {
                            used.insert(fv);
                        }
                    }
                }
            }
        }
    }
}

fn collect_used_from_value(value: &Value, used: &mut HashSet<String>) {
    match value {
        Value::Unit => {}
        Value::Pair(a, b) => {
            collect_used_from_value(a, used);
            collect_used_from_value(b, used);
        }
        Value::Inl(v) | Value::Inr(v) => collect_used_from_value(v, used),
        Value::Neutral(n) => collect_used_from_neutral(n, used),
        Value::Kont(k) => {
            for frame in &k.frames {
                collect_used_from_frame(frame, used);
            }
        }
        Value::Closure {
            param, body, env, ..
        } => {
            for fv in free_vars_term(body) {
                if fv != *param {
                    match env.lookup(&fv) {
                        Some(v) => collect_used_from_value(v, used),
                        None => {
                            used.insert(fv);
                        }
                    }
                }
            }
        }
    }
}

struct ReadBackState {
    top_kont_var: Option<String>,
    used: HashSet<String>,
}

fn alloc_name(state: &mut ReadBackState, base: &str) -> String {
    if !state.used.contains(base) {
        state.used.insert(base.to_string());
        return base.to_string();
    }
    let trimmed = base.trim_end_matches(|c: char| c.is_ascii_digit());
    let stem = if trimmed.is_empty() { base } else { trimmed };
    let mut idx = 1usize;
    loop {
        let candidate = format!("{}{}", stem, idx);
        if !state.used.contains(&candidate) {
            state.used.insert(candidate.clone());
            return candidate;
        }
        idx += 1;
    }
}

fn read_back_term_in_env(term: &Term, env: &Env, state: &mut ReadBackState) -> Term {
    match term {
        Term::Var(name) => match env.lookup(name) {
            Some(val) => read_back_value(val, state),
            None => Term::Var(name.clone()),
        },
        Term::Unit => Term::Unit,
        Term::Lam {
            param,
            param_ty,
            body,
        } => {
            let fresh = alloc_name(state, param);
            let ext = env.extend(param.clone(), Value::Neutral(Neutral::Var(fresh.clone())));
            let new_body = read_back_term_in_env(body, &ext, state);
            Term::lam(fresh, param_ty.clone(), new_body)
        }
        Term::App(f, a) => Term::app(
            read_back_term_in_env(f, env, state),
            read_back_term_in_env(a, env, state),
        ),
        Term::Pair(l, r) => Term::pair(
            read_back_term_in_env(l, env, state),
            read_back_term_in_env(r, env, state),
        ),
        Term::Fst(e) => Term::fst(read_back_term_in_env(e, env, state)),
        Term::Snd(e) => Term::snd(read_back_term_in_env(e, env, state)),
        Term::Inl(e) => Term::inl(read_back_term_in_env(e, env, state)),
        Term::Inr(e) => Term::inr(read_back_term_in_env(e, env, state)),
        Term::Case {
            scrutinee,
            left_var,
            left_body,
            right_var,
            right_body,
        } => {
            let s = read_back_term_in_env(scrutinee, env, state);
            let xl = alloc_name(state, left_var);
            let lb = read_back_term_in_env(
                left_body,
                &env.extend(left_var.clone(), Value::Neutral(Neutral::Var(xl.clone()))),
                state,
            );
            let xr = alloc_name(state, right_var);
            let rb = read_back_term_in_env(
                right_body,
                &env.extend(right_var.clone(), Value::Neutral(Neutral::Var(xr.clone()))),
                state,
            );
            Term::Case {
                scrutinee: Box::new(s),
                left_var: xl,
                left_body: Box::new(lb),
                right_var: xr,
                right_body: Box::new(rb),
            }
        }
        Term::Absurd(e, ty) => Term::absurd(read_back_term_in_env(e, env, state), ty.clone()),
        Term::Ann(e, _) => read_back_term_in_env(e, env, state),
        Term::CallCC {
            param,
            param_ty,
            body,
        } => {
            let fresh = alloc_name(state, param);
            let ext = env.extend(param.clone(), Value::Neutral(Neutral::Var(fresh.clone())));
            let new_body = read_back_term_in_env(body, &ext, state);
            Term::callcc(fresh, param_ty.clone(), new_body)
        }
        Term::Throw {
            cont,
            value,
            target_ty,
        } => Term::throw(
            read_back_term_in_env(cont, env, state),
            read_back_term_in_env(value, env, state),
            target_ty.clone(),
        ),
    }
}

fn read_back_neutral(neutral: &Neutral, state: &mut ReadBackState) -> Term {
    match neutral {
        Neutral::Var(name) => Term::Var(name.clone()),
        Neutral::App(n, v) => {
            Term::app(read_back_neutral(n, state), read_back_value(v, state))
        }
        Neutral::Fst(n) => Term::fst(read_back_neutral(n, state)),
        Neutral::Snd(n) => Term::snd(read_back_neutral(n, state)),
        Neutral::Absurd(n, ty) => Term::absurd(read_back_neutral(n, state), ty.clone()),
        Neutral::Throw {
            cont,
            value,
            target_ty,
        } => Term::throw(
            read_back_neutral(cont, state),
            read_back_value(value, state),
            target_ty.clone(),
        ),
        Neutral::Case {
            scrutinee,
            left_var,
            left_body,
            right_var,
            right_body,
            env,
        } => {
            let s = read_back_neutral(scrutinee, state);
            let xl = alloc_name(state, left_var);
            let ext_l = env.extend(left_var.clone(), Value::Neutral(Neutral::Var(xl.clone())));
            let lb = if closure_is_effectful(left_var, left_body, env) {
                read_back_term_in_env(left_body, &ext_l, state)
            } else {
                match eval_with_env(left_body, &ext_l) {
                    Ok(v) => read_back_value(&v, state),
                    Err(_) => read_back_term_in_env(left_body, &ext_l, state),
                }
            };
            let xr = alloc_name(state, right_var);
            let ext_r = env.extend(right_var.clone(), Value::Neutral(Neutral::Var(xr.clone())));
            let rb = if closure_is_effectful(right_var, right_body, env) {
                read_back_term_in_env(right_body, &ext_r, state)
            } else {
                match eval_with_env(right_body, &ext_r) {
                    Ok(v) => read_back_value(&v, state),
                    Err(_) => read_back_term_in_env(right_body, &ext_r, state),
                }
            };
            Term::Case {
                scrutinee: Box::new(s),
                left_var: xl,
                left_body: Box::new(lb),
                right_var: xr,
                right_body: Box::new(rb),
            }
        }
    }
}

fn read_back_value(value: &Value, state: &mut ReadBackState) -> Term {
    match value {
        Value::Unit => Term::Unit,
        Value::Pair(a, b) => Term::pair(read_back_value(a, state), read_back_value(b, state)),
        Value::Inl(v) => Term::inl(read_back_value(v, state)),
        Value::Inr(v) => Term::inr(read_back_value(v, state)),
        Value::Neutral(n) => read_back_neutral(n, state),
        Value::Closure {
            param,
            param_ty,
            body,
            env,
        } => {
            let fresh = alloc_name(state, param);
            let ext = env.extend(param.clone(), Value::Neutral(Neutral::Var(fresh.clone())));
            let body_term = if closure_is_effectful(param, body, env) {
                read_back_term_in_env(body, &ext, state)
            } else {
                match eval_with_env(body, &ext) {
                    Ok(res) => read_back_value(&res, state),
                    Err(_) => read_back_term_in_env(body, &ext, state),
                }
            };
            Term::lam(fresh, param_ty.clone(), body_term)
        }
        Value::Kont(kont) => {
            if kont.frames.is_empty() {
                let k_name = match &state.top_kont_var {
                    Some(existing) => existing.clone(),
                    None => {
                        let fresh = alloc_name(state, "k");
                        state.top_kont_var = Some(fresh.clone());
                        fresh
                    }
                };
                return Term::Var(k_name);
            }
            let hole = alloc_name(state, "v");
            let mut acc = Term::Var(hole.clone());
            for frame in kont.frames.iter().rev() {
                acc = match frame {
                    Frame::AppArg { arg, env } => {
                        Term::app(acc, read_back_term_in_env(arg, env, state))
                    }
                    Frame::AppFn { func } => Term::app(read_back_value(func, state), acc),
                    Frame::PairRight { right, env } => {
                        Term::pair(acc, read_back_term_in_env(right, env, state))
                    }
                    Frame::PairLeft { left } => Term::pair(read_back_value(left, state), acc),
                    Frame::Fst => Term::fst(acc),
                    Frame::Snd => Term::snd(acc),
                    Frame::Inl => Term::inl(acc),
                    Frame::Inr => Term::inr(acc),
                    Frame::Absurd(ty) => Term::absurd(acc, ty.clone()),
                    Frame::ThrowVal {
                        value,
                        env,
                        target_ty,
                    } => Term::throw(acc, read_back_term_in_env(value, env, state), target_ty.clone()),
                    Frame::ThrowCont { cont, target_ty } => {
                        Term::throw(read_back_value(cont, state), acc, target_ty.clone())
                    }
                    Frame::Case {
                        left_var,
                        left_body,
                        right_var,
                        right_body,
                        env,
                    } => {
                        let xl = alloc_name(state, left_var);
                        let lb = read_back_term_in_env(
                            left_body,
                            &env.extend(left_var.clone(), Value::Neutral(Neutral::Var(xl.clone()))),
                            state,
                        );
                        let xr = alloc_name(state, right_var);
                        let rb = read_back_term_in_env(
                            right_body,
                            &env.extend(
                                right_var.clone(),
                                Value::Neutral(Neutral::Var(xr.clone())),
                            ),
                            state,
                        );
                        Term::Case {
                            scrutinee: Box::new(acc),
                            left_var: xl,
                            left_body: Box::new(lb),
                            right_var: xr,
                            right_body: Box::new(rb),
                        }
                    }
                };
            }
            Term::lam(hole, None, acc)
        }
    }
}

pub fn read_back(value: &Value) -> Term {
    let mut used = HashSet::new();
    collect_used_from_value(value, &mut used);
    let mut state = ReadBackState {
        top_kont_var: None,
        used,
    };
    let body = read_back_value(value, &mut state);
    match state.top_kont_var {
        Some(k) => Term::callcc(k, None, body),
        None => body,
    }
}

pub fn normalize(term: &Term) -> Term {
    match eval(term) {
        Ok(val) => read_back(&val),
        Err(_) => term.clone(),
    }
}

pub fn normalize_with_env(term: &Term, env: &[(String, Term)]) -> Term {
    let mut cek_env = Env::new();
    for (name, def) in env {
        let val = match eval_with_env(def, &cek_env) {
            Ok(v) => v,
            Err(_) => return normalize(term),
        };
        cek_env = cek_env.extend(name.clone(), val);
    }
    match eval_with_env(term, &cek_env) {
        Ok(val) => read_back(&val),
        Err(_) => term.clone(),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::parser::{parse_term, parse_type};
    use crate::typecheck::{check, Context};

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

    #[test]
    fn cek_throw_aborts_pending_frames() {
        let term = parse_term("callcc k. fst (throw k (), ((), ()))").unwrap();
        assert_eq!(eval(&term).unwrap(), Value::Unit);
        assert_eq!(normalize(&term), Term::Unit);
    }

    #[test]
    fn cek_executes_peirce_and_lem_backtracking() {
        let peirce_run = parse_term(
            "(\\(f : (Top -> Bot) -> Top). callcc (k : Cont Top). f (\\a. throw k a)) (\\g. absurd (g ()))",
        )
        .unwrap();
        let ty = Type::Top;
        check(&Context::new(), &peirce_run, &ty).unwrap();
        assert_eq!(eval(&peirce_run).unwrap(), Value::Unit);

        let lem_run = parse_term(
            "case (callcc (k : Cont (Either Top (Top -> Void))). inr (\\a. throw k (inl a))) of inl u => (u, ()) | inr not_top => absurd (not_top ())",
        )
        .unwrap();
        let pair_ty = parse_type("Top * Top").unwrap();
        check(&Context::new(), &lem_run, &pair_ty).unwrap();
        let val = eval(&lem_run).unwrap();
        assert_eq!(val, Value::Pair(Box::new(Value::Unit), Box::new(Value::Unit)));
        assert_eq!(read_back(&val).to_string(), "((), ())");
    }

    #[test]
    fn cek_read_back_lem_preserves_subject_reduction() {
        let lem = parse_term("callcc k. inr (\\a. throw k (inl a))").unwrap();
        let ty = parse_type("Either A (A -> Void)").unwrap();
        check(&Context::new(), &lem, &ty).unwrap();
        let norm = normalize(&lem);
        check(&Context::new(), &norm, &ty).unwrap();
    }
}
