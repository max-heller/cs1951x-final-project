import data.set

import .formula
import .derivations
import .tactics
import .logics
import .consistency
import .enumeration

open_locale classical

/-- As set `s` is complete if, for any formula `x`, either `x` or `¬x` is contained in `s`. -/
def set.complete (s : set formula) := ∀x, x ∈ s ∨ (¬x) ∈ s

/-- As set `s` is complete `Σ`-consistent if it is complete and `Σ`-consistent. -/
def set.complete_consistent (s : set formula) (axms) := s.consistent axms ∧ s.complete

def ccₙ (s axms : set formula) : ℕ → set formula
| 0 := s
| (n + 1) := if (ccₙ n ∪ {enumerate n}).consistent axms
  then ccₙ n ∪ {enumerate n}
  else ccₙ n ∪ {¬enumerate n}

/-- `cc s Σ` constructs a complete, `Σ`-consistent set built upon `s`. -/
def cc (s : set formula) (axms) : set formula := ⋃n, ccₙ s axms n

lemma ccₙ_sub_cc (s) (axms) (n : ℕ) : ccₙ s axms n ⊆ cc s axms :=
begin
  intros x hn,
  rw cc,
  rw set.mem_Union,
  apply exists.intro n,
  assumption,
end

lemma ccₙ_sub_ccₘ' (s axms) (n m) : ccₙ s axms n ⊆ ccₙ s axms (n + m) :=
begin
  intros x hn,
  induction m,
  { assumption, },
  { rw nat.add_succ,
    rw ccₙ,
    by_cases (ccₙ s axms (n + m_n) ∪ {enumerate (n + m_n)}).consistent axms,
    { simp [h, m_ih], },
    { simp [h, m_ih], }, },
end

lemma ccₙ_sub_ccₘ (s axms) (n m : ℕ) (hm : m ≥ n) : ccₙ s axms n ⊆ ccₙ s axms m :=
begin
  have h := ccₙ_sub_ccₘ' s axms n (m - n),
  simp [nat.add_sub_of_le hm] at h,
  assumption,
end

lemma ccₙ_consistent (s axms : set formula) (n : ℕ) (h₀ : s.consistent axms) :
  (ccₙ s axms n).consistent axms :=
begin
  induction n,
  { simp [ccₙ, h₀], },
  { rw ccₙ,
    by_cases (ccₙ s axms n_n ∪ {enumerate n_n}).consistent axms;
    have h' := consistent_extensible (ccₙ s axms n_n) axms n_ih (enumerate n_n),
    { simp [h] at *,
      assumption, },
    { simp [h] at *,
      exact or.resolve_left h' h, }, },
end

lemma minimal_ccₙ (s axms : set formula) (xs : list formula) (hxs : ∀x ∈ xs, x ∈ cc s axms) :
  ∃n, ∀x ∈ xs, x ∈ ccₙ s axms n :=
begin
  induction xs with _ _ ih,
  { simp, },
  { have hxs' : ∀ (x : formula), x ∈ xs_tl → x ∈ cc s axms := begin
      intros x hx,
      apply hxs,
      apply or.intro_right,
      exact hx,
    end,
    apply exists.elim (ih hxs'),
    intros n hn,
    have hx := hxs xs_hd (or.intro_left _ (by refl)),
    rw [cc, set.mem_Union] at hx,
    apply exists.elim hx,
    intros n' hn',
    apply exists.intro (max n n'),
    intros a ha,
    cases ha,
    { apply ccₙ_sub_ccₘ s axms n' _,
      { simp, },
      { simp [ha, hn'], }, },
    { apply ccₙ_sub_ccₘ s axms n _,
      { simp },
      { apply hn,
        exact ha, }, }, },
end

lemma cc_consistent (s axms : set formula) (h₀ : s.consistent axms) :
  (cc s axms).consistent axms :=
begin
  by_contradiction,
  simp [set.consistent] at h,
  apply exists.elim h,
  intros xs hxs,
  clear h,
  cases hxs with hxs hdb,
  have h := minimal_ccₙ s axms xs hxs,
  apply exists.elim h,
  intros n hn,
  have hnc := ccₙ_consistent s axms n h₀,
  apply not.elim hnc,
  apply exists.intro xs,
  split,
  assumption',
end

/-- For any complete, `Σ` consistent set `s`, there exists a complete, `Σ`-consistent set built upon `s`. -/
theorem lindenbaum (s : set formula) (axms) (hcc : s.complete_consistent axms) :
  ∃s' ⊇ s, s'.complete_consistent axms :=
begin
  apply exists.intro (cc s axms),
  split,
  { intros x hx,
    rw [cc, set.mem_Union],
    apply exists.intro 0,
    rw ccₙ,
    assumption, },
  { split,
    { cases hcc,
      exact cc_consistent s axms hcc_left, },
    { rw set.complete,
      intros x,
      apply exists.elim (enumerate.complete x),
      intros n hn,
      rw [cc, set.mem_Union, set.mem_Union],
      cases classical.em (((ccₙ s axms n) ∪ {x}).consistent axms),
      { apply or.intro_left,
        apply exists.intro (n + 1),
        simp at h,
        simp [ccₙ, hn, h], },
      { apply or.intro_right,
        apply exists.intro (n + 1),
        simp at h,
        simp [ccₙ, hn, h], }, }, },
end

lemma derivable_iff_mem_cc (axms Γ : set formula) (a : formula) :
  (Γ ⊢[axms] a) ↔ (∀s ⊇ Γ, s.complete_consistent axms → a ∈ s) :=
sorry

def set.canonical_model (axms : set formula) : model :=
{
  world := set formula,
  w := {Δ | Δ.complete_consistent axms},
  r := λΔ Δ', {a | (□a) ∈ Δ} ⊆ Δ',
  v := λp, {Δ | formula.symbol p ∈ Δ},
}

@[simp] lemma set.canonical_model.w (axms : set formula) : axms.canonical_model.w = {Δ | Δ.complete_consistent axms} :=
by refl

/-- The Truth Lemma: a world `Δ` in the canonical model of a system makes a formula true
    iff the formula is contained in `Δ`. -/
theorem truth_lemma (axms : set formula) {hc : has_mem formula axms.canonical_model.world} :
  ∀a w, (⟨axms.canonical_model, w⟩ ⊩ a) ↔ a ∈ w :=
sorry

@[simp] lemma not_in_complete_consistent (axms Γ : set formula) (hcc : Γ.complete_consistent axms) (a : formula) :
  a ∉ Γ ↔ (¬a) ∈ Γ :=
begin
  apply iff.intro,
  { intro h,
    cases hcc with _ hc,
    rw set.complete at hc,
    apply or.resolve_left (hc a) h, },
  { intro h,
    cases hcc with hc _,
    rw set.consistent at hc,
    by_contradiction ha,
    apply hc,
    have hdna := derivable.reflexivity (¬a) h,
    apply derivable.from.mp a,
    { apply derivable.from.mp ¬a,
      { apply derivable.monotonicity ∅,
        tauto,
        rw derivable.from.no_premises,
        tactic.derive_taut (¬0 ⟶ 0 ⟶ ⊥), },
      { exact hdna, }, },
    apply derivable.reflexivity a ha, },
end

lemma deductive_closure {axms : set formula} (Γ : set formula) (hcc : Γ.complete_consistent axms) (a : formula) :
  (Γ ⊢[axms] a) → a ∈ Γ :=
begin
  intro ha,
  by_contradiction,
  rw not_in_complete_consistent axms at h,
  { cases hcc with h₁ h₂,
    apply h₁,
    apply derivable.from.mp a,
    { apply derivable.from.mp ¬a,
      { apply derivable.monotonicity ∅,
        tauto,
        rw derivable.from.no_premises,
        tactic.derive_taut (¬0 ⟶ 0 ⟶ ⊥), },
      { apply derivable.reflexivity,
        assumption, }, },
    assumption, },
  assumption,
end

/-- Determination: the canonical model for `Σ` satisfies a formula iff the formula is `Σ`-derivable. -/
theorem determination (axms : set formula) : ∀a, (axms.canonical_model ⊩ a) ↔ (axms ⊢ a) :=
begin
  intro a,
  apply iff.intro,
  { intro ha,
    rw [←derivable.from.no_premises, derivable_iff_mem_cc],
    intros s _ hs,
    rw ←truth_lemma axms,
    apply ha,
    assumption, },
  { intros h w hw,
    rw truth_lemma,
    apply deductive_closure,
    { simp at hw,
      exact hw, },
    { apply derivable.monotonicity ∅,
      { tauto, },
      { rw derivable.from.no_premises,
        assumption, }, }, },
end

/-- A system `Σ` is complete for a set `𝒞` of models iff for any formula `a`, `𝒞 ⊨ a → Σ ⊢ a`. -/
class complete (axms : set formula) (𝒞 : set model) :=
(complete : ∀a, (𝒞 ⊨ a) → (axms ⊢ a))

/-- The normal modal logic `K` is complete with respect to the set of all models. -/
instance logic.k.complete : complete logic.k set.univ :=
{ complete :=
  begin
    intro a,
    contrapose,
    rw ←determination,
    intro h,
    tautology,
  end }