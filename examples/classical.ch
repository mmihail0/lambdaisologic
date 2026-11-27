-- classical axioms
theorem peirce : ((A -> B) -> A) -> A =
  \f. callcc k. f (\a. throw k a)

theorem dne : ((A -> Void) -> Void) -> A =
  \dn. callcc k. absurd (dn (\a. throw k a))

theorem lem : Either A (A -> Void) =
  callcc k. inr (\a. throw k (inl a))

theorem classical_demorgan : ((A * B) -> Void) -> Either (A -> Void) (B -> Void) =
  \nab. callcc k. inl (\a. throw k (inr (\b. nab (a, b))))

-- cek machine evaluation tests
theorem eval_peirce : Top =
  (\(f : (Top -> Void) -> Top). callcc (k : Cont Top). f (\a. throw k a)) (\g. absurd (g ()))

theorem eval_dne : Top =
  (\(dn : (Top -> Void) -> Void). callcc (k : Cont Top). absurd (dn (\a. throw k a))) (\k. k ())

theorem eval_lem : Top * Top =
  case (callcc (k : Cont (Either Top (Top -> Void))). inr (\a. throw k (inl a))) of
    | inl u => (u, ())
    | inr not_top => absurd (not_top ())

theorem eval_classical_demorgan : Top =
  case ((\(nab : (Top * Void) -> Void). callcc (k : Cont (Either (Top -> Void) (Void -> Void))). inl (\a. throw k (inr (\b. nab (a, b))))) (\p. snd p)) of
    | inl not_top => absurd (not_top ())
    | inr not_bot => ((\(f : Void -> Void). ()) not_bot)
