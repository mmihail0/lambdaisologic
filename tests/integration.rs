use std::fs;
use std::path::PathBuf;
use std::process::Command;
use std::time::{SystemTime, UNIX_EPOCH};

use curry_howard::eval::{eval, normalize, normalize_with_env, read_back, EvalError, Value};
use curry_howard::parser::{parse_program, parse_term, parse_type};
use curry_howard::search::{prove, prove_classical, DEFAULT_SEARCH_DEPTH};
use curry_howard::syntax::{Term, Type};
use curry_howard::typecheck::{check, check_declaration, check_program, synthesize, Context, TypeError};

fn unique_temp_path(name: &str) -> PathBuf {
    let nanos = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .unwrap()
        .as_nanos();
    std::env::temp_dir().join(format!("curry_howard_{}_{}_{}.ch", name, std::process::id(), nanos))
}

#[test]
fn examples_logic_file_checks_and_subject_reduction_holds() {
    let path = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("examples")
        .join("logic.ch");
    let source = fs::read_to_string(&path).unwrap();
    let decls = parse_program(&source).unwrap();
    assert_eq!(decls.len(), 9);

    let ctx = check_program(&decls).unwrap();
    assert_eq!(ctx.len(), 9);

    let mut norm_env: Vec<(String, Term)> = Vec::new();
    for decl in &decls {
        let norm = normalize_with_env(&decl.proof, &norm_env);
        check(&Context::new(), &norm, &decl.ty).unwrap_or_else(|e| {
            panic!(
                "normalized term '{}' for '{}' failed subject reduction: {}",
                norm, decl.name, e
            )
        });
        norm_env.push((decl.name.clone(), norm));
    }
}

#[test]
fn examples_classical_file_checks_and_evaluates() {
    let path = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("examples")
        .join("classical.ch");
    let source = fs::read_to_string(&path).unwrap();
    let decls = parse_program(&source).unwrap();
    assert_eq!(decls.len(), 8);

    let ctx = check_program(&decls).unwrap();
    assert_eq!(ctx.len(), 8);

    let mut norm_env: Vec<(String, Term)> = Vec::new();
    for decl in &decls {
        let norm = normalize_with_env(&decl.proof, &norm_env);
        check(&Context::new(), &norm, &decl.ty).unwrap_or_else(|e| {
            panic!(
                "normalized term '{}' for '{}' failed subject reduction: {}",
                norm, decl.name, e
            )
        });
        match decl.name.as_str() {
            "eval_peirce" | "eval_dne" | "eval_classical_demorgan" => {
                assert_eq!(norm, Term::Unit, "{} must normalize to ()", decl.name);
            }
            "eval_lem" => {
                assert_eq!(
                    norm,
                    Term::pair(Term::Unit, Term::Unit),
                    "eval_lem must normalize to ((), ())"
                );
            }
            _ => {}
        }
        norm_env.push((decl.name.clone(), norm));
    }
}

#[test]
fn parser_unicode_comments_and_error_locations() {
    let slash_line = concat!("/", "/");
    let block_open = concat!("/", "*");
    let block_close = concat!("*", "/");
    let src = format!(
        "{} line comment\n{} multi\nline {} theorem unicode_law : A ∧ B → B ∨ A = fn p => inr (fst p)",
        slash_line, block_open, block_close
    );
    let decls = parse_program(&src).unwrap();
    assert_eq!(decls.len(), 1);
    assert_eq!(decls[0].name, "unicode_law");
    check_program(&decls).unwrap();

    let err_arrow = parse_type("A ->\nB ->").unwrap_err();
    assert_eq!(err_arrow.line, 2);
    assert_eq!(err_arrow.col, 5);

    let err_case = parse_term("case x of\n  inl a => a").unwrap_err();
    assert_eq!(err_case.line, 2);
    assert_eq!(err_case.col, 13);

    let err_trailing = parse_type("A -> B C").unwrap_err();
    assert_eq!(err_trailing.line, 1);
    assert_eq!(err_trailing.col, 8);

    let unclosed = format!("theorem ok : A -> A = \\x. x\n{} unclosed", block_open);
    let err_comment = parse_program(&unclosed).unwrap_err();
    assert_eq!(err_comment.line, 2);
    assert_eq!(err_comment.col, 1);

    let err_cc = parse_term("call/cc k =>\n  throw k").unwrap_err();
    assert_eq!(err_cc.line, 2);
    assert_eq!(err_cc.col, 10);
}

#[test]
fn bidirectional_type_errors_cover_all_variants() {
    let empty = Context::new();

    let e1 = synthesize(&empty, &parse_term("z").unwrap()).unwrap_err();
    assert!(matches!(e1, TypeError::UnboundVariable { .. }));
    assert!(e1.to_string().contains("unbound variable"));

    let e2 = check(
        &empty,
        &parse_term("\\x. ()").unwrap(),
        &parse_type("A -> B").unwrap(),
    )
    .unwrap_err();
    assert!(matches!(e2, TypeError::TypeMismatch { .. }));
    assert!(e2.to_string().contains("expected B, found Top"));

    let e3 = check(
        &empty,
        &parse_term("\\(x : B). x").unwrap(),
        &parse_type("A -> A").unwrap(),
    )
    .unwrap_err();
    assert!(matches!(e3, TypeError::AnnotationMismatch { .. }));
    assert!(e3.to_string().contains("expected A, found B"));

    let e4 = synthesize(&empty, &parse_term("\\(x : A). x x").unwrap()).unwrap_err();
    assert!(matches!(e4, TypeError::ExpectedFunction { .. }));
    assert!(e4.to_string().contains("found A"));

    let e5 = check(
        &empty,
        &parse_term("\\x. x").unwrap(),
        &parse_type("A * B").unwrap(),
    )
    .unwrap_err();
    assert!(matches!(e5, TypeError::ExpectedFunctionForLambda { .. }));
    assert!(e5.to_string().contains("expected A * B"));

    let e6 = synthesize(&empty, &parse_term("\\(x : A). fst x").unwrap()).unwrap_err();
    assert!(matches!(e6, TypeError::ExpectedProduct { .. }));

    let e7 = synthesize(
        &empty,
        &parse_term("\\(x : A). case x of inl u => u | inr v => v").unwrap(),
    )
    .unwrap_err();
    assert!(matches!(e7, TypeError::ExpectedSum { .. }));

    let e8 = synthesize(
        &empty,
        &parse_term("\\(s : A + B). case s of inl u => u | inr v => v").unwrap(),
    )
    .unwrap_err();
    assert!(matches!(e8, TypeError::BranchTypeMismatch { .. }));
    assert!(e8.to_string().contains("left branch has type A"));
    assert!(e8.to_string().contains("right branch has type B"));

    let e9 = synthesize(&empty, &parse_term("inl a").unwrap()).unwrap_err();
    assert!(matches!(e9, TypeError::CannotSynthesize { .. }));

    let e10 = check(
        &empty,
        &parse_term("inl ()").unwrap(),
        &parse_type("Top * Top").unwrap(),
    )
    .unwrap_err();
    assert!(matches!(e10, TypeError::CannotCheck { .. }));

    let e11 = synthesize(&empty, &parse_term("callcc (k : A). k").unwrap()).unwrap_err();
    assert!(matches!(e11, TypeError::ExpectedContinuation { .. }));
}

#[test]
fn classical_laws_fail_without_callcc() {
    let empty = Context::new();
    assert!(check(
        &empty,
        &parse_term("\\dn. absurd (dn (\\a. a))").unwrap(),
        &parse_type("((A -> Void) -> Void) -> A").unwrap(),
    )
    .is_err());
    assert!(check(
        &empty,
        &parse_term("inr (\\a. a)").unwrap(),
        &parse_type("Either A (A -> Void)").unwrap(),
    )
    .is_err());
    assert!(check(
        &empty,
        &parse_term("\\f. f (\\a. absurd a)").unwrap(),
        &parse_type("((A -> B) -> A) -> A").unwrap(),
    )
    .is_err());
    assert!(check(
        &empty,
        &parse_term("\\nab. inl (\\a. nab (a, a))").unwrap(),
        &parse_type("((A * B) -> Void) -> Either (A -> Void) (B -> Void)").unwrap(),
    )
    .is_err());
}

#[test]
fn evaluator_normalization_and_capture_avoidance() {
    let nested = parse_term(
        "\\f a b. (\\(g : A * A -> C). g (fst (a, b), snd (b, a))) (\\p. case (inl (fst p) : A + A) of inl x => f x b | inr y => f y b)",
    )
    .unwrap();
    let check_ty = parse_type("(A -> B -> C) -> A -> B -> C").unwrap();
    check(&Context::new(), &nested, &check_ty).unwrap();
    let norm = normalize(&nested);
    assert_eq!(norm.to_string(), "\\f. \\a. \\b. f a b");
    check(&Context::new(), &norm, &check_ty).unwrap();

    let case_capture = parse_term("(\\y. case s of inl x => y | inr x => x) x").unwrap();
    let replaced = normalize(&case_capture);
    let expected = parse_term("case s of inl x1 => x | inr x2 => x2").unwrap();
    assert_eq!(replaced, expected);

    let absurd_ty = Type::arrow(Type::Bot, Type::Atom("A".into()));
    let absurd_term = parse_term("\\e. ((\\z : Top. absurd e) : Top -> A) ()").unwrap();
    check(&Context::new(), &absurd_term, &absurd_ty).unwrap();
    let absurd_norm = normalize(&absurd_term);
    assert_eq!(absurd_norm.to_string(), "\\e. absurd e");
    check(&Context::new(), &absurd_norm, &absurd_ty).unwrap();
}

#[test]
fn cek_machine_continuation_capture_and_errors() {
    let abort_pair = parse_term("callcc k. (throw k ((), ()), absurd ())").unwrap();
    let val = eval(&abort_pair).unwrap();
    assert_eq!(val, Value::Pair(Box::new(Value::Unit), Box::new(Value::Unit)));
    assert_eq!(read_back(&val), Term::pair(Term::Unit, Term::Unit));

    let reentrant = parse_term(
        "(\\(mk : Top -> Either Top (Top -> Void)). case (mk ()) of inl u => (u, case (mk ()) of inl v => v | inr g => absurd[Top] (g ())) | inr g => absurd[Top * Top] (g ())) (\\z. callcc k. inr (\\a. throw k (inl a)))",
    )
    .unwrap();
    check(&Context::new(), &reentrant, &parse_type("Top * Top").unwrap()).unwrap();
    assert_eq!(
        eval(&reentrant).unwrap(),
        Value::Pair(Box::new(Value::Unit), Box::new(Value::Unit))
    );

    let frame_reenter = parse_term(
        "case (callcc (k : Cont (Either Top (Cont (Either Top Top)))). inr k) of inl u => u | inr k2 => throw k2 (inl ())",
    )
    .unwrap();
    assert_eq!(eval(&frame_reenter).unwrap(), Value::Unit);

    assert!(matches!(
        eval(&parse_term("() ()").unwrap()).unwrap_err(),
        EvalError::InvalidApplication(Value::Unit)
    ));
    assert!(matches!(
        eval(&parse_term("fst ()").unwrap()).unwrap_err(),
        EvalError::InvalidProjection(Value::Unit)
    ));
    assert!(matches!(
        eval(&parse_term("case () of inl x => x | inr y => y").unwrap()).unwrap_err(),
        EvalError::InvalidCaseScrutinee(Value::Unit)
    ));
    assert!(matches!(
        eval(&parse_term("absurd ()").unwrap()).unwrap_err(),
        EvalError::InvalidAbsurd(Value::Unit)
    ));
    assert!(matches!(
        eval(&parse_term("throw () ()").unwrap()).unwrap_err(),
        EvalError::InvalidContinuation(Value::Unit)
    ));
    assert!(matches!(
        eval(&parse_term("case (callcc k. inl k) of inl k2 => throw k2 (inl k2) | inr u => u").unwrap()).unwrap_err(),
        EvalError::StepLimitExceeded
    ));
}

#[test]
fn automated_search_roundtrips_and_separates_classical_from_intuitionistic() {
    let provable_intuitionistic = [
        "A -> A",
        "A -> (A -> B) -> B",
        "A * B -> B * A",
        "A + B -> B + A",
        "(A * B -> C) -> A -> B -> C",
        "(A -> B -> C) -> A * B -> C",
        "Bot -> A",
        "~(A + B) -> ~A * ~B",
        "~A * ~B -> ~(A + B)",
        "~A + ~B -> ~(A * B)",
        "~~(A + ~A)",
        "~~(((A -> B) -> A) -> A)",
        "(A + B -> C) -> (A -> C) * (B -> C)",
        "(A -> C) * (B -> C) -> A + B -> C",
    ];

    for prop in provable_intuitionistic {
        let ty = parse_type(prop).unwrap();
        let term = prove(&ty, DEFAULT_SEARCH_DEPTH)
            .unwrap_or_else(|| panic!("expected proof for '{}'", prop));
        let printed = term.to_string();
        let reparsed = parse_term(&printed).unwrap_or_else(|e| {
            panic!("failed to reparse printed proof '{}' for '{}': {}", printed, prop, e)
        });
        check(&Context::new(), &reparsed, &ty).unwrap_or_else(|e| {
            panic!("reparsed proof '{}' failed check for '{}': {}", reparsed, prop, e)
        });
    }

    let classical_only = [
        "A + ~A",
        "~~A -> A",
        "((A -> B) -> A) -> A",
        "~(A * B) -> ~A + ~B",
        "(~A -> ~B) -> B -> A",
        "Either A (A -> Void)",
        "((A * B) -> Void) -> Either (A -> Void) (B -> Void)",
    ];

    for prop in classical_only {
        let ty = parse_type(prop).unwrap();
        assert!(
            prove(&ty, DEFAULT_SEARCH_DEPTH).is_none(),
            "classical-only proposition '{}' must not be proved intuitionistically",
            prop
        );
        let c_term = prove_classical(&ty, DEFAULT_SEARCH_DEPTH)
            .unwrap_or_else(|| panic!("expected classical proof for '{}'", prop));
        let printed = c_term.to_string();
        let reparsed = parse_term(&printed).unwrap_or_else(|e| {
            panic!("failed to reparse classical proof '{}' for '{}': {}", printed, prop, e)
        });
        check(&Context::new(), &reparsed, &ty).unwrap_or_else(|e| {
            panic!(
                "reparsed classical proof '{}' failed check for '{}': {}",
                reparsed, prop, e
            )
        });
    }

    let decls = parse_program("theorem t : A -> A = \\x. x").unwrap();
    check_declaration(&Context::new(), &decls[0]).unwrap();
}

#[test]
fn cli_binary_check_and_prove_workflows() {
    let bin = env!("CARGO_BIN_EXE_curry-howard");
    let logic_path = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("examples")
        .join("logic.ch");
    let classical_path = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("examples")
        .join("classical.ch");

    let check_ok = Command::new(bin)
        .arg("check")
        .arg(&logic_path)
        .output()
        .unwrap();
    assert!(check_ok.status.success());
    let stdout_ok = String::from_utf8_lossy(&check_ok.stdout);
    assert!(stdout_ok.contains("[OK] modus_ponens"));
    assert!(stdout_ok.contains("[OK] demorgan_or_not_to_not_and"));
    assert!(stdout_ok.contains("normalized:"));

    let check_classical = Command::new(bin)
        .arg("check")
        .arg(&classical_path)
        .output()
        .unwrap();
    assert!(check_classical.status.success());
    let stdout_cl = String::from_utf8_lossy(&check_classical.stdout);
    assert!(stdout_cl.contains("[OK] peirce"));
    assert!(stdout_cl.contains("[OK] dne"));
    assert!(stdout_cl.contains("[OK] lem"));
    assert!(stdout_cl.contains("[OK] classical_demorgan"));
    assert!(stdout_cl.contains("[OK] eval_peirce"));
    assert!(stdout_cl.contains("[OK] eval_lem"));

    let bad_path = unique_temp_path("bad_theorem");
    fs::write(&bad_path, "theorem broken : A -> B = \\x. x\n").unwrap();
    let check_fail = Command::new(bin)
        .arg("--check")
        .arg(&bad_path)
        .output()
        .unwrap();
    let _ = fs::remove_file(&bad_path);
    assert!(!check_fail.status.success());
    let stderr_fail = String::from_utf8_lossy(&check_fail.stderr);
    assert!(stderr_fail.contains("[FAIL] broken"));
    assert!(stderr_fail.contains("expected B, found A"));

    let prove_ok = Command::new(bin)
        .args(["prove", "A * B -> B * A"])
        .output()
        .unwrap();
    assert!(prove_ok.status.success());
    let prove_stdout = String::from_utf8_lossy(&prove_ok.stdout);
    assert!(prove_stdout.contains("[PROVED] (intuitionistic)"));
    assert!(prove_stdout.contains("proof:"));

    let prove_depth_fail = Command::new(bin)
        .args(["prove", "--depth", "1", "A -> B -> A"])
        .output()
        .unwrap();
    assert!(!prove_depth_fail.status.success());
    assert!(String::from_utf8_lossy(&prove_depth_fail.stderr).contains("[UNPROVABLE]"));

    let prove_classical_denied = Command::new(bin)
        .args(["--prove", "A + ~A"])
        .output()
        .unwrap();
    assert!(!prove_classical_denied.status.success());
    assert!(String::from_utf8_lossy(&prove_classical_denied.stderr).contains("[UNPROVABLE]"));

    let prove_classical_ok = Command::new(bin)
        .args(["prove", "--classical", "((A -> B) -> A) -> A"])
        .output()
        .unwrap();
    assert!(prove_classical_ok.status.success());
    let prove_cl_stdout = String::from_utf8_lossy(&prove_classical_ok.stdout);
    assert!(prove_cl_stdout.contains("[PROVED] (classical)"));
    assert!(prove_cl_stdout.contains("callcc"));

    let prove_non_tautology = Command::new(bin)
        .args(["prove", "--classical", "A -> B"])
        .output()
        .unwrap();
    assert!(!prove_non_tautology.status.success());
    assert!(String::from_utf8_lossy(&prove_non_tautology.stderr).contains("[UNPROVABLE]"));

    let help_out = Command::new(bin).arg("--help").output().unwrap();
    assert!(help_out.status.success());
    assert!(String::from_utf8_lossy(&help_out.stdout).contains("--classical"));

    let bad_args = Command::new(bin).output().unwrap();
    assert!(!bad_args.status.success());
}
