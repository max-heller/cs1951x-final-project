import tactic.basic

/-- Attempts to automatically show the derivability of a tautology. -/
meta def derive_taut : tactic unit :=
do
  tactic.applyc `derivable.taut,
  `[simp [tautology]],
  tactic.tautology {classical := tt} <|> tactic.skip