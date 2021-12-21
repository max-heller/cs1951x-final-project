import .formula
import .semantics
import .tactics

/-- A formula `a` is `Σ`-derivable iff it has a valid derivation from the axioms in `Σ`. -/
inductive derivable (axms : set formula) : formula → Prop
| k (a b : formula) : derivable (k a b)
| dual (a : formula) : derivable (dual a)
| taut (a : formula) (ha : tautology a) : derivable a
| axm (axm ∈ axms) (a : formula) (h : substitution_inst axm a) : derivable a
| mp (a b : formula) (hab : derivable (a ⟶ b)) (ha : derivable a) : derivable b
| nec {a : formula} (ha : derivable a) : derivable □a

reserve prefix `⊢ ` :15
reserve infix ` ⊢ ` :15

notation axms ⊢ a := derivable axms a
notation ⊢ a := ∅ ⊢ a

/-- A formula `a` is `Σ`-derivable from a set of premises `Γ` iff `Σ ⊢ C₁ → ⋯ → Cₙ → a` for some `{Cᵢ} ⊆ Γ`. -/
@[simp] def derivable.from (axms : set formula) (Γ : set formula) (a : formula) : Prop :=
∃xs, (∀x ∈ xs, x ∈ Γ) ∧ (axms ⊢ list.foldr formula.implies a xs)

notation Γ ` ⊢[`axms`] ` a := derivable.from axms Γ a

def derivable.from.rev {axms : set formula} (Γ : set formula) (Γ' : list formula) (a : formula) :
  (∀x ∈ Γ', x ∈ Γ) → (axms ⊢ Γ'.foldr formula.implies a) → (Γ ⊢[axms] a) :=
begin
  intros hΓ' hd,
  apply exists.intro Γ',
  tautology,
end

lemma all_antecedents {v : symbol → Prop} {mv : formula → Prop} (a : formula) (xs : list formula) :
  satisfies v mv (xs.foldr formula.implies a) ↔ (∀x ∈ xs, satisfies v mv x) → satisfies v mv a :=
begin
  apply iff.intro,
  { induction xs,
    { simp, },
    { intros ha hxs,
      simp at ha,
      apply xs_ih,
      { apply ha,
        apply hxs,
        simp, },
      { intros x hx,
        simp at hxs,
        apply hxs.elim_right,
        assumption, }, }, },
  { intro hxs,
    induction xs,
    { simp [hxs], },
    { simp,
      intro h,
      apply xs_ih,
      intros h,
      apply hxs,
      intros x hx,
      cases hx,
      { rw hx,
        assumption, },
      { apply h,
        exact hx, }, }, },
end

lemma derivable.redundant_premises {axms : set formula} {Γ : list formula} {a : formula} (Γ' ⊆ Γ) :
  (axms ⊢ Γ'.foldr formula.implies a) → (axms ⊢ Γ.foldr formula.implies a) :=
begin
  intro hΓ',
  apply derivable.mp (Γ'.foldr formula.implies a) _ _ hΓ',
  clear hΓ',
  derive_taut,
  intros v mv hΓ',
  rw all_antecedents at *,
  intro hΓ,
  apply hΓ',
  intros x hx,
  apply hΓ,
  apply H,
  assumption,
end

lemma derivable.from.exact {axms : set formula} (Γ : list formula) (a : formula) :
  (axms ⊢ Γ.foldr formula.implies a) ↔ ((λx, x ∈ Γ) ⊢[axms] a) :=
begin
  apply iff.intro,
  { intro h,
    apply derivable.from.rev (λx, x ∈ Γ) Γ,
    { tauto, },
    { assumption, }, },
  { intro h,
    cases h with xs hxs,
    cases hxs with hxs hd,
    have hxs' : xs ⊆ Γ := hxs,
    exact derivable.redundant_premises xs hxs hd, },
end

@[simp] lemma derivable.from.no_premises (axms : set formula) (a : formula) :
  (∅ ⊢[axms] a) ↔ (axms ⊢ a) :=
begin
  apply iff.intro,
  { intro h,
    cases h with xs hxs,
    cases hxs with hxs ha,
    cases xs,
    { simp [hxs] at ha,
      assumption, },
    { apply false.elim,
      apply hxs xs_hd,
      simp, }, },
  { intro h,
    apply exists.intro [],
    split,
    { tauto, },
    { exact h, }, },
end

lemma derivable.monotonicity {axms : set formula} (Γ Γ' : set formula) {a : formula} :
  Γ ⊆ Γ' → (Γ ⊢[axms] a) → (Γ' ⊢[axms] a) :=
begin
  intros hp hd,
  apply exists.elim hd,
  intros xs h,
  cases h,
  apply exists.intro xs,
  split,
  { intros x hx,
    apply hp,
    apply h_left x hx, },
  { assumption, }
end

lemma derivable.reflexivity {axms Γ : set formula} (a : formula) :
  a ∈ Γ → (Γ ⊢[axms] a) :=
begin
  intros ha,
  apply exists.intro [a],
  simp [ha],
  derive_taut,
end

lemma foldr_deduction (a b) (xs) :
  list.foldr formula.implies (b ⟶ a) xs = list.foldr formula.implies a (xs ++ [b]) :=
by simp

lemma derivable.deduction (axms : set formula) (Γ : set formula) (a b : formula) :
  (Γ ∪ {b} ⊢[axms] a) ↔ (Γ ⊢[axms] b ⟶ a) :=
begin
  apply iff.intro,
  { intro hda,
    cases hda with xs h,
    cases h with hxs hda,
    apply exists.intro (xs.filter (λx, x ≠ b)),
    split,
    { intros x hx,
      rw list.mem_filter at hx,
      have hx' : x ∈ xs := by simp [hx],
      apply or.elim (hxs x hx'),
      { tauto, },
      { intros hxb,
        apply not.elim (and.elim_right hx),
        cases hxb,
        refl, }, },
    { apply derivable.mp (xs.foldr formula.implies a) _ _ hda,
      derive_taut,
      intros v mv hsa,
      rw all_antecedents at *,
      intro h,
      simp,
      intro hsb,
      apply hsa,
      clear hsa,
      intros x hx,
      by_cases (x = b),
        { simp * at *, },
        { simp * at *, }, }, },
  { intro hdba,
    cases hdba,
    cases hdba_h,
    apply exists.intro (hdba_w ++ [b]),
    split,
    { intros x hx,
      simp at hx,
      cases hx,
      { apply or.intro_left,
        apply hdba_h_left x hx, },
      { apply or.intro_right,
        tauto, }, },
    { rw foldr_deduction at hdba_h_right,
      assumption, }, }
end

lemma mp_from_premises {v : symbol → Prop} {mv : formula → Prop} (a b : formula) (Γ : list formula)
    (hab : satisfies v mv (Γ.foldr formula.implies (a ⟶ b))) (ha : satisfies v mv (Γ.foldr formula.implies a)) :
  satisfies v mv (Γ.foldr formula.implies b) :=
begin
  induction Γ,
  { simp * at *, },
  { simp * at *,
    intro hhd,
    simp * at *, },
end

lemma derivable.from.mp {axms Γ : set formula} (a b : formula)
    (hab : Γ ⊢[axms] (a ⟶ b)) (ha : Γ ⊢[axms] a) :
  Γ ⊢[axms] b :=
begin
  cases hab with xs hxs,
  cases hxs with hxs hdab,
  cases ha with ys hys,
  cases hys with hys hda,
  apply exists.intro (xs ++ ys),
  split,
  { intros x hx,
    simp at hx,
    cases hx,
    { apply hxs, assumption, },
    { apply hys, assumption, }, },
  { apply derivable.mp (list.foldr formula.implies a (xs ++ ys)),
    { apply derivable.mp (list.foldr formula.implies (a ⟶ b) (xs ++ ys)),
      { derive_taut,
        intros v mv h₁ h₂,
        rw ←list.foldr_append at *,
        exact mp_from_premises a b (xs ++ ys) h₁ h₂, },
      { apply derivable.redundant_premises xs,
        { simp, },
        { assumption, } }, },
    { apply derivable.redundant_premises ys,
      { simp },
      { assumption }, }, },
end

lemma derivable.cut (axms : set formula) (Γ Γ' : set formula) (a b : formula) :
  (Γ ⊢[axms] a) → (Γ' ∪ {a} ⊢[axms] b) → (Γ ∪ Γ' ⊢[axms] b) :=
begin
  intros hda hdb,
  rw derivable.deduction at hdb,
  apply derivable.from.mp a b,
  { apply derivable.monotonicity Γ' _ _ hdb,
    simp, },
  { apply derivable.monotonicity Γ _ _ hda,
    simp, },
end

example (a b : formula) : ⊢ (a ∨ ¬a) ∧ (b ∨ ¬b) :=
by derive_taut

example (a b c : formula) : ⊢ (a ⟶ b) ⟶ (b ⟶ c) ⟶ (a ⟶ c) :=
by derive_taut

lemma box_and (a b : formula) : ⊢ □(a ∧ b) ⟶ (□a ∧ □b) :=
begin
  apply derivable.mp (□(a ∧ b) ⟶ □b),
  { apply derivable.mp (□(a ∧ b) ⟶ □a),
    { derive_taut, },
    { apply derivable.mp,
      { apply derivable.k (a ∧ b) a, },
      { apply derivable.nec,
        derive_taut, } } },
  { apply derivable.mp,
    { apply derivable.k, },
    { apply derivable.nec,
      derive_taut, } },
end