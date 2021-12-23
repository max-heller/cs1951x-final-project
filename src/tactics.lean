import tactic.basic

meta def ignore_premises : tactic unit :=
do
  `[apply derivable.monotonicity ∅],
  tactic.tautology,
  `[rw derivable.from.no_premises]

/-- Attempts to automatically show the derivability of a tautology. -/
meta def derive_taut : tactic unit :=
do
  ignore_premises <|> tactic.skip,
  tactic.applyc `derivable.taut,
  `[simp [tautology]],
  tactic.tautology {classical := tt} <|> tactic.skip