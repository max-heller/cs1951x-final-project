import data.set

import .formula
import .derivations
import .tactics
import .logics
import .consistency
import .enumeration

open_locale classical

reserve prefix `□⁻¹` :40
reserve prefix `◇⁻¹` :40

notation □⁻¹Γ := {a | (□a) ∈ Γ}
notation ◇⁻¹Γ := {a | (◇a) ∈ Γ}
notation □Γ := {(□a) | a ∈ Γ}
notation ◇Γ := {(◇a) | a ∈ Γ}

/-- As set `s` is complete if, for any formula `x`, either `x` or `¬x` is contained in `s`. -/
def set.complete (s : set formula) := ∀x, x ∈ s ∨ (¬x) ∈ s

/-- As set `s` is complete `Σ`-consistent if it is complete and `Σ`-consistent. -/
def set.complete_consistent (s : set formula) (axms) := s.consistent axms ∧ s.complete

@[simp] lemma set.complete_consistent.not_mem_iff {axms : set formula} {Γ : set formula} (hcc : Γ.complete_consistent axms) {a : formula} :
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
    have hdna := derivable.reflexivity h,
    apply derivable.from.mp a,
    { apply derivable.from.mp ¬a,
      { derive_taut, },
      { exact hdna, }, },
    apply derivable.reflexivity ha, },
end

lemma set.complete_consistent.deductive_closure {axms : set formula} {Γ : set formula} (hcc : Γ.complete_consistent axms) (a : formula) :
  (Γ ⊢[axms] a) → a ∈ Γ :=
begin
  intro ha,
  by_contradiction,
  rw set.complete_consistent.not_mem_iff at h,
  { cases hcc with h₁ h₂,
    apply h₁,
    apply derivable.from.mp a,
    { apply derivable.from.mp ¬a,
      { derive_taut, },
      { apply derivable.reflexivity,
        assumption, }, },
    assumption, },
  assumption,
end

lemma set.complete_consistent.not_mem_bot {axms} {Γ : set formula} (hΓ : Γ.complete_consistent axms) :
  formula.bottom ∉ Γ :=
begin
  by_contradiction,
  apply hΓ.elim_left,
  exact derivable.reflexivity h,
end

lemma set.complete_consistent.mem_top {axms} {Γ : set formula} (hΓ : Γ.complete_consistent axms) :
  formula.top ∈ Γ :=
begin
  apply set.complete_consistent.deductive_closure hΓ,
  derive_taut,
end

lemma set.complete_consistent.mem_and {axms} {Γ : set formula} (hΓ : Γ.complete_consistent axms) {a b : formula} :
  (a ∧ b) ∈ Γ ↔ a ∈ Γ ∧ b ∈ Γ :=
begin
  apply iff.intro,
  { intro h,
    split,
    repeat {
      apply set.complete_consistent.deductive_closure hΓ,
      apply derivable.from.mp (a ∧ b) _ _ (derivable.reflexivity h),
      derive_taut,
    }, },
  { intro h,
    apply set.complete_consistent.deductive_closure hΓ,
    apply derivable.from.mp a,
    apply derivable.from.mp b,
    derive_taut,
    exact derivable.reflexivity (and.elim_right h),
    exact derivable.reflexivity (and.elim_left h), },
end

lemma set.complete_consistent.mem_or {axms} {Γ : set formula} (hΓ : Γ.complete_consistent axms) {a b : formula} :
  (a ∨ b) ∈ Γ ↔ a ∈ Γ ∨ b ∈ Γ :=
begin
  apply iff.intro,
  { intro h,
    { by_contradiction h',
      apply not.elim _ h,
      rw set.complete_consistent.not_mem_iff hΓ,
      apply set.complete_consistent.deductive_closure hΓ,
      apply derivable.from.mp (¬a),
      apply derivable.from.mp (¬b),
      derive_taut,
      repeat {
        apply derivable.reflexivity,
        rw ←set.complete_consistent.not_mem_iff hΓ,
        tauto,
      }, }, },
  { intro h,
    apply set.complete_consistent.deductive_closure hΓ,
    cases h,
    { apply derivable.from.mp _ _ _ (derivable.reflexivity h),
      derive_taut, },
    { apply derivable.from.mp _ _ _ (derivable.reflexivity h),
      derive_taut, }, },
end

lemma set.complete_consistent.mem_imp {axms} {Γ : set formula} (hΓ : Γ.complete_consistent axms) {a b : formula} :
  (a ⟶ b) ∈ Γ ↔ a ∈ Γ → b ∈ Γ :=
begin
  apply iff.intro,
  { intro h,
    { by_contradiction h',
      apply not.elim _ h,
      rw set.complete_consistent.not_mem_iff hΓ,
      apply set.complete_consistent.deductive_closure hΓ,
      apply derivable.from.mp a,
      apply derivable.from.mp (¬b),
      derive_taut,
      { apply derivable.reflexivity,
        rw ←set.complete_consistent.not_mem_iff hΓ,
        tauto, },
      { apply derivable.reflexivity,
        tauto, }, }, },
  { intro h,
    apply set.complete_consistent.deductive_closure hΓ,
    have h := not_or_of_imp h,
    cases h,
    { rw set.complete_consistent.not_mem_iff hΓ at h_1,
      apply derivable.from.mp _ _ _ (derivable.reflexivity h_1),
      derive_taut, },
    { apply derivable.from.mp _ _ _ (derivable.reflexivity h_1),
      derive_taut, }, },
end

lemma set.complete_consistent.mem_iff {axms} {Γ : set formula} (hΓ : Γ.complete_consistent axms) {a b : formula} :
  (a ↔ b) ∈ Γ ↔ (a ∈ Γ ↔ b ∈ Γ) :=
begin
  apply iff.intro,
  { intro h,
    apply iff.intro,
    repeat {
      intro h',
      apply set.complete_consistent.deductive_closure hΓ,
      apply derivable.from.mp _ _ _ (derivable.reflexivity h'),
      apply derivable.from.mp _ _ _ (derivable.reflexivity h),
      derive_taut,
    }, },
  { intro h,
    apply set.complete_consistent.deductive_closure hΓ,
    by_cases ha : a ∈ Γ,
    { apply derivable.from.mp _ _ _ (derivable.reflexivity ha),
      apply derivable.from.mp _ _ _ (derivable.reflexivity (h.mp ha)),
      derive_taut, },
    { have hna := (set.complete_consistent.not_mem_iff hΓ).mp ha,
      have hnb := (set.complete_consistent.not_mem_iff hΓ).mp ((iff_false_left ha).mp h),
      apply derivable.from.mp _ _ _ (derivable.reflexivity hna),
      apply derivable.from.mp _ _ _ (derivable.reflexivity hnb),
      derive_taut, }, },
end

lemma derive_imp_derive_box {axms} {Γ : set formula} {a : formula} :
  (Γ ⊢[axms] a) → (□Γ ⊢[axms] □a) :=
begin
  intro hda,
  cases hda with xs hxs,
  cases hxs with hxs hda,
  apply exists.intro (xs.map (λa, □a)),
  split,
  { intros x hx,
    simp * at *,
    cases hx with a ha,
    apply exists.intro a,
    simp *, },
  { exact derivable.RK hda, },
end

lemma debox_derive_imp_derive_box {axms} {Γ : set formula} {a : formula} :
  (□⁻¹Γ ⊢[axms] a) → (Γ ⊢[axms] □a) :=
begin
  intro hda,
  cases hda with xs hxs,
  cases hxs with hxs hda,
  apply exists.intro (xs.map (λa, □a)),
  split,
  { intros x hx,
    simp * at *,
    cases hx with a ha,
    rw ←ha.elim_right,
    apply hxs,
    exact ha.elim_left, },
  { exact derivable.RK hda, },
end

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

/-- For any `Σ` consistent set `s`, there exists a complete, `Σ`-consistent set built upon `s`. -/
theorem lindenbaum {axms : set formula} {s : set formula} (hcc : s.consistent axms) :
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
    { exact cc_consistent s axms hcc, },
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
  (Γ ⊢[axms] a) ↔ (∀Δ ⊇ Γ, Δ.complete_consistent axms → a ∈ Δ) :=
begin
  apply iff.intro,
  { intros hda Δ hΔ hcc,
    by_contradiction,
    cases hcc with hconsistent hcomplete,
    apply hconsistent,
    apply derivable.from.mp a,
    { apply derivable.from.mp ¬a,
      { derive_taut, },
      { rw set.complete at hcomplete,
        apply derivable.reflexivity,
        exact or.resolve_left (hcomplete a) h, }, },
    { exact derivable.monotonicity Γ Δ hΔ hda, }, },
  { intros h,
    by_contradiction hnc,
    rw [derivable_iff_not_consistent, not_not] at hnc,
    cases lindenbaum hnc with Δ hΔ,
    cases hΔ with hΔ hΔcc,
    apply @not.elim (a ∈ Δ),
    { rw set.complete_consistent.not_mem_iff hΔcc,
      apply set.mem_of_subset_of_mem hΔ,
      simp, },
    { refine h Δ _ hΔcc,
      intros x hx,
      exact hΔ (or.intro_left _ hx), }, },
end

lemma set.complete_consistent.mem_box {axms} {Γ : set formula} (hΓ : Γ.complete_consistent axms) {a : formula} :
  (□a) ∈ Γ ↔ ∀Δ : set formula, Δ.complete_consistent axms → (□⁻¹Γ) ⊆ Δ → a ∈ Δ :=
begin
  apply iff.intro,
  { intros hba Δ hΔcc hΔ,
    apply hΔ,
    exact hba, },
  { contrapose,
    intros hnba h,
    have hndba : ¬(Γ ⊢[axms] □a) := begin
      by_contradiction,
      apply hnba,
      exact set.complete_consistent.deductive_closure hΓ _ h,
    end,
    have hndba' : ¬(□⁻¹Γ ⊢[axms] a) := begin
      by_contradiction,
      apply hndba,
      exact debox_derive_imp_derive_box h,
    end,
    have hnc := (iff_false_left hndba').mp derivable_iff_not_consistent,
    rw not_not at hnc,
    cases lindenbaum hnc with Δ hΔ,
    cases hΔ with hΔ hΔcc, 
    apply not.elim,
    { change a ∉ Δ,
      intro ha,
      apply hΔcc.elim_left,
      apply derivable.from.mp a _ _ (derivable.reflexivity ha),
      apply derivable.from.mp ¬a,
      derive_taut,
      apply derivable.reflexivity,
      apply hΔ,
      simp, },
    { apply h Δ hΔcc,
      intros x hx,
      apply hΔ,
      exact or.intro_left _ hx, }, },
end

lemma set.complete_consistent.debox_subset_iff {axms} {Γ Δ : set formula}
    (hΓ : Γ.complete_consistent axms) (hΔ : Δ.complete_consistent axms) :
  (□⁻¹Γ) ⊆ Δ ↔ (◇Δ) ⊆ Γ :=
begin
  apply iff.intro,
  { intros h x hx,
    cases hx with a ha,
    cases ha with ha hx,
    rw ←hx at *,
    clear hx x,
    apply set.complete_consistent.deductive_closure hΓ,
    apply derivable.from.mp ¬□¬a,
    { apply derivable.from.mp (dual a),
      { derive_taut, },
      { ignore_premises,
        apply derivable.dual, }, },
    { apply derivable.reflexivity,
      apply (hΓ.elim_right _).resolve_left,
      by_contradiction h',
      apply not.elim _ ha,
      rw set.complete_consistent.not_mem_iff hΔ,
      exact h h', }, },
  { intros h a,
    simp at h,
    contrapose,
    intro ha,
    change (□a) ∉ Γ,
    rw set.complete_consistent.not_mem_iff hΓ,
    apply set.complete_consistent.deductive_closure hΓ,
    { rw derivable.from.not_box_iff_diamond_not,
      apply derivable.reflexivity,
      rw set.complete_consistent.not_mem_iff hΔ at ha,
      apply h,
      simp,
      exact ha, }, },
end

lemma set.complete_consistent.mem_diamond {axms} {Γ : set formula} (hΓ : Γ.complete_consistent axms) {a : formula} :
  (◇a) ∈ Γ ↔ ∃Δ : set formula, Δ.complete_consistent axms ∧ (◇Δ) ⊆ Γ ∧ a ∈ Δ :=
begin
  -- have h₁ : (◇a) ∈ Γ ↔ (¬□¬a) ∈ Γ := sorry,
  -- have h₂ : (¬□¬a) ∈ Γ ↔ (□¬a) ∉ Γ := sorry,
  -- have h₃ := set.complete_consistent.mem_box hΓ,
  sorry
end

def set.canonical_model (axms : set formula) : model :=
{
  world := set formula,
  w := {Δ | Δ.complete_consistent axms},
  r := λΔ Δ', (□⁻¹Δ) ⊆ Δ',
  v := λp, {Δ | formula.symbol p ∈ Δ},
}

@[simp] lemma set.canonical_model.w (axms : set formula) : axms.canonical_model.w = {Δ | Δ.complete_consistent axms} :=
by refl

@[simp] lemma set.canonical_model.world (axms : set formula) : axms.canonical_model.world = set formula :=
by refl

@[simp] lemma set.canonical_model.v {axms : set formula} : axms.canonical_model.v = λp : symbol, {Δ : set formula | formula.symbol p ∈ Δ} :=
by refl

@[simp] lemma set.canonical_model.r {axms : set formula} : axms.canonical_model.r = λΔ Δ' : set formula, (□⁻¹Δ) ⊆ Δ' :=
by refl

/-- The Truth Lemma: a world `Δ` in the canonical model of a system makes a formula true
    iff the formula is contained in `Δ`. -/
theorem truth_lemma {axms : set formula} {Δ : set formula} {hΔ : Δ ∈ axms.canonical_model.w} :
  ∀a, (⟨axms.canonical_model, Δ⟩ ⊩ a) ↔ a ∈ Δ :=
begin
  intros a,
  simp * at *,
  induction a generalizing Δ,
  { simp,
    exact set.complete_consistent.not_mem_bot hΔ, },
  { simp,
    exact set.complete_consistent.mem_top hΔ, },
  { simp, exact iff.rfl, },
  { simp * at *,
    apply set.complete_consistent.not_mem_iff hΔ, },
  { simp * at *,
    exact iff.symm (set.complete_consistent.mem_and hΔ), },
  { simp * at *,
    exact iff.symm (set.complete_consistent.mem_or hΔ), },
  { simp * at *,
    exact iff.symm (set.complete_consistent.mem_imp hΔ), },
  { simp * at *,
    exact iff.symm (set.complete_consistent.mem_iff hΔ), },
  { apply iff.intro,
    { intro hba,
      simp at hba,
      apply (set.complete_consistent.mem_box hΔ).mpr,
      intros Δ' hΔ'cc hΔ',
      rw ←a_ih hΔ'cc,
      exact hba Δ' hΔ'cc hΔ', },
    { intro hba,
      intros Δ' hΔ' hrΔ',
      rw a_ih hΔ',
      apply hrΔ',
      exact hba, }, },
  { apply iff.intro,
    { intro hda,
      simp at hda,
      apply (set.complete_consistent.mem_diamond hΔ).mpr,
      cases hda with Δ' hΔ',
      cases hΔ' with hΔ'cc hΔ',
      cases hΔ' with hΔ' hΔ'a,
      apply exists.intro Δ',
      split,
      exact hΔ'cc,
      split,
      { intros x hx,
        rw set.complete_consistent.debox_subset_iff hΔ hΔ'cc at hΔ',
        apply hΔ',
        exact hx, },
      { rw ←a_ih hΔ'cc,
        exact hΔ'a, }, },
    { contrapose,
      intro hnda,
      rw set.complete_consistent.not_mem_iff hΔ,
      have hbna : ⟨axms.canonical_model, Δ⟩ ⊩ □¬a_a := begin
        intros Δ' hΔ' hΔ'r,
        by_contradiction,
        apply hnda,
        apply exists.intro Δ',
        apply exists.intro hΔ',
        split,
        exact hΔ'r,
        simp at h,
        exact h,
      end,
      apply set.complete_consistent.deductive_closure hΔ,
      sorry }, },
end

/-- Determination: the canonical model for `Σ` satisfies a formula iff the formula is `Σ`-derivable. -/
theorem determination (axms : set formula) : ∀a, (axms.canonical_model ⊩ a) ↔ (axms ⊢ a) :=
begin
  intro a,
  apply iff.intro,
  { intro ha,
    rw [←derivable.from.no_premises, derivable_iff_mem_cc],
    intros s _ hs,
    rw ←truth_lemma,
    apply ha,
    assumption', },
  { intros h w hw,
    rw truth_lemma,
    apply set.complete_consistent.deductive_closure,
    { simp at hw,
      exact hw, },
    { apply derivable.monotonicity ∅,
      { tauto, },
      { rw derivable.from.no_premises,
        assumption, }, },
    assumption, },
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