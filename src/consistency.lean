import .formula
import .derivations

/-- A set `s` is `Σ`-consistent if it does not `Σ`-derive `⊥`.  -/
def set.consistent (s axms : set formula) : Prop := ¬(s ⊢[axms] ⊥)

lemma consistent_extensible (Γ : set formula) (axms) :
  Γ.consistent axms → ∀a, (Γ ∪ {a}).consistent axms ∨ (Γ ∪ {¬a}).consistent axms :=
begin
  contrapose,
  simp only [not_forall],
  intro h,
  cases h with a ha,
  simp [set.consistent, -derivable.from] at ha,
  rw ←and_iff_not_or_not at ha,
  cases ha with ha hna,
  rw [set.consistent, not_not],
  rw [←set.union_singleton, derivable.deduction] at *,
  apply derivable.from.mp (a ⟶ ⊥) _ _ ha,
  apply derivable.from.mp (¬a ⟶ ⊥) _ _ hna,
  apply derivable.monotonicity ∅,
  { simp, },
  { rw derivable.from.no_premises,
    derive_taut, },
end