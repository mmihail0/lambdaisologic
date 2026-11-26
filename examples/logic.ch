-- propositional logic
theorem modus_ponens : A -> (A -> B) -> B =
  \a f. f a

-- conjunction and disjunction
theorem and_comm : A * B -> B * A =
  \p. (snd p, fst p)

theorem or_comm : A + B -> B + A =
  \s. case s of
    | inl x => inr x
    | inr y => inl y

-- currying
theorem curry : (A * B -> C) -> A -> B -> C =
  \f a b. f (a, b)

theorem uncurry : (A -> B -> C) -> A * B -> C =
  \f p. f (fst p) (snd p)

-- ex falso quodlibet
theorem ex_falso : Bot -> A =
  \e. absurd e

-- de morgan laws
theorem demorgan_not_or_to_and_not : ~(A + B) -> ~A * ~B =
  \f. (\a. f (inl a), \b. f (inr b))

theorem demorgan_and_not_to_not_or : ~A * ~B -> ~(A + B) =
  \p s. case s of
    | inl a => fst p a
    | inr b => snd p b

theorem demorgan_or_not_to_not_and : ~A + ~B -> ~(A * B) =
  \s p. case s of
    | inl na => na (fst p)
    | inr nb => nb (snd p)
