import .formula
import .derivations

/-- A set `s` is `Σ`-consistent if it does not `Σ`-derive `⊥`.  -/
def set.consistent (s axms : set formula) : Prop := ¬(s ⊢[axms] ⊥)

lemma consistent_iff_any_nonderivable (Γ : set formula) (axms) :
  Γ.consistent axms ↔ ∃a, ¬(Γ ⊢[axms] a) :=
sorry

lemma derivable_iff_not_inconsistent (Γ : set formula) (axms) (a) :
  (Γ ⊢[axms] a) ↔ ¬Γ.consistent (axms ∪ {¬a}) :=
sorry

lemma consistent_extensible (Γ : set formula) (axms) :
  Γ.consistent axms → ∀a, (Γ ∪ {a}).consistent axms ∨ (Γ ∪ {¬a}).consistent axms :=
begin
  contrapose,
  simp only [not_forall],
  intro h,
  apply exists.elim h,
  intros a ha,
  sorry
end