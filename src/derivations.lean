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
∃xs, (∀x ∈ xs, x ∈ Γ) ∧ (axms ⊢ (list.foldr formula.implies a xs))

notation Γ ` ⊢[`axms`] ` a := derivable.from axms Γ a

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

lemma derivable.monotonicity {axms : set formula} (Γ Γ' : set formula) (a : formula) :
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

lemma derivable.cut (axms : set formula) (Γ Γ' : set formula) (a b : formula) :
  (Γ ⊢[axms] a) → ((Γ' ∪ {a}) ⊢[axms] b) → ((Γ ∪ Γ') ⊢[axms] b) :=
begin
  intros hda hdb,
  sorry
end

lemma foldr_deduction (a b) (xs) :
  list.foldr formula.implies (b ⟶ a) xs = list.foldr formula.implies a (xs ++ [b]) :=
by simp

lemma derivable.deduction (axms : set formula) (Γ : set formula) (a b : formula) :
  (Γ ∪ {b} ⊢[axms] a) ↔ (Γ ⊢[axms] b ⟶ a) :=
begin
  apply iff.intro,
  { intro hda,
    apply exists.elim hda,
    clear hda,
    intros xs h,
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
    { induction xs,
      { simp at *,
        apply derivable.mp a,
        { derive_taut, },
        { assumption, }, },
      { simp at *,
        sorry } } },
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
  { sorry }
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