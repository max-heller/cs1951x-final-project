import tactic.basic
import tactic.interactive

import .formula

/-- A formula is satisfied by an assignment if it evaluates to true. -/
@[simp] def satisfies (asgn : symbol → Prop) : formula → Prop
| ⊤ := true
| ⊥ := false
| (formula.symbol s) := asgn s
| ¬a := ¬satisfies a
| (a ∧ b) := satisfies a ∧ satisfies b
| (a ∨ b) := satisfies a ∨ satisfies b
| (a ⟶ b) := satisfies a → satisfies b
| (a ↔ b) := satisfies a ↔ satisfies b
| □a := false
| ◇a := false

/-- A tautology is a formula that is always true. -/
structure tautology :=
(a : formula)
{modal_free : modal_free a}
(taut : ∀asgn, satisfies asgn a)

/-- A model is a collection of worlds with a relation and an interpretation function that
    determines at which worlds sentence symbols are true. -/
structure model :=
{world : Type}
(w : set world)
(r : world → world → Prop)
(v : symbol → set world)

/-- Definition of truth at a world in a model. -/
@[simp] def truth (m : model) : m.world → formula → Prop
| _ ⊥ := false
| _ ⊤ := true
| w (formula.symbol s) := w ∈ (m.v s)
| w ¬a := ¬truth w a
| w (a ∧ b) := truth w a ∧ truth w b
| w (a ∨ b) := truth w a ∨ truth w b
| w (a ⟶ b) := truth w a → truth w b
| w (a ↔ b) := truth w a ↔ truth w b
| w □a := ∀w' ∈ m.w, m.r w w' → truth w' a
| w ◇a := ∃w' ∈ m.w, m.r w w' ∧ truth w' a

notation ⟨m, w⟩ ` ⊩ ` a := truth m w a

/-- A formula is true in a model iff it is true in all worlds in the model. -/
@[simp] def true_in (m : model) (a : formula) := ∀w ∈ m.w, ⟨m, w⟩ ⊩ a

reserve infix ` ⊩ ` :15
notation m ⊩ a := true_in m a

/-- A formula is true in a set of models iff it is true in all models in the set. -/
@[simp] def valid (𝒞 : set model) (a : formula) := ∀m ∈ 𝒞, m ⊩ a

reserve prefix `⊨ ` :15
reserve infix ` ⊨ ` :15

notation 𝒞 ⊨ a := valid 𝒞 a
notation ⊨ a := set.univ ⊨ a

@[simp] lemma valid_imp_valid_in (a : formula) {ha : ⊨ a} {𝒞 : set model} : 𝒞 ⊨ a :=
begin
  intros m _,
  apply ha,
  tautology,
end

@[simp] def k (a b : formula) := □(a ⟶ b) ⟶ (□a ⟶ □b)

theorem k.valid : ∀(a b : formula), ⊨ k a b :=
begin
  intros a b,
  intros m _ w hw,
  intros h₁ h₂,
  intros w' _ hr,
  apply h₁,
  assumption',
  apply h₂,
  assumption',
end

@[simp] def dual (a : formula) := ◇a ↔ ¬□¬a

theorem dual.valid : ∀a : formula, ⊨ dual a :=
begin
  intro a,
  intros m _ w hw,
  apply iff.intro,
  { intro h₁,
    intro h₂,
    simp at *,
    apply exists.elim h₁,
    intros w' hw',
    cases hw',
    cases hw'_right,
    apply h₂ w',
    assumption', },
  { intro h₁,
    simp at *,
    assumption, }
end

theorem foo (a : formula) (ha : modal_free a) (substs : symbol → formula)
    (v : symbol → Prop) (m : model) (w ∈ m.w)
    (hv : ∀s, v s ↔ ⟨m, w⟩ ⊩ substs s) :
  satisfies v a ↔ ⟨m, w⟩ ⊩ subst substs a :=
begin
  induction a,
  repeat { simp },
  { apply hv a, },
  { simp [a_ih ha], },
  repeat { simp [a_ih_a (and.left ha), a_ih_b (and.right ha)], },
  repeat { simp at ha, contradiction, },
end

/-- All substitution instances of tautologies are valid. -/
theorem tautology.valid (taut : tautology) (a : formula) :
  substitution_inst taut.a a → ⊨ a :=
begin
  contrapose,
  intros h₁ h₂,
  simp at h₁,
  apply exists.elim h₁,
  intros m hm,
  cases hm with w hw,
  cases hw,
  apply hw_right,
  rw substitution_inst at h₂,
  apply exists.elim h₂,
  intros substs hs,
  let asgn := λs, ⟨m, w⟩ ⊩ substs s,
  have x := foo taut.a taut.modal_free substs asgn m w _ _,
  simp [←hs, ←x],
  apply taut.taut,
  { assumption, },
  { simp, },
end

theorem mp (a b : formula) (m : model) (w ∈ m.w) : (⟨m, w⟩ ⊩ a ⟶ b) → (⟨m, w⟩ ⊩ a) → (⟨m, w⟩ ⊩ b) :=
begin
  intros hab ha,
  apply hab,
  assumption,
end

theorem mp_valid {𝒞 : set model} (a b : formula) : (𝒞 ⊨ a ⟶ b) → (𝒞 ⊨ a) → (𝒞 ⊨ b) :=
begin
  intros hab ha m _ w _,
  apply mp,
  assumption',
  apply hab,
  assumption',
  apply ha,
  assumption',
end

theorem nec_valid {𝒞 : set model} (a : formula) : (𝒞 ⊨ a) → (𝒞 ⊨ □a) :=
begin
  intro ha,
  intros m _ w _,
  intros w' _ hww',
  apply ha,
  assumption',
end