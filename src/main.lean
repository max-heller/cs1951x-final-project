import tactic.alias

alias string ← symbol

inductive formula : Type
| bottom : formula
| top : formula
| symbol : symbol → formula
| not : formula → formula
| and : formula → formula → formula
| or : formula → formula → formula
| implies : formula → formula → formula
| iff : formula → formula → formula
| box : formula → formula
| diamond : formula → formula

reserve infixr ` ⟶ ` :(std.prec.arrow+1)
reserve prefix `□` :40
reserve prefix `◇` :40

notation `⊥` := formula.bottom
notation `⊤` := formula.top
notation ¬ a := formula.not a
notation a ∧ b := (formula.and a b)
notation a ∨ b := formula.or a b
notation a ` ⟶ ` b := formula.implies a b
notation a ↔ b := formula.iff a b
notation □a := formula.box a
notation ◇a := formula.diamond a

-- notation `⊥` := formula.bottom
-- notation `⊤` := formula.top
-- prefix `¬` :40 := formula.not
-- infix ` ∧ ` :35 := formula.and
-- infix ` ∨ ` :30 := formula.or
-- infix ` ↔ ` :20 := formula.iff
-- prefix `□` :40 := formula.box
-- prefix `◇` :40 := formula.diamond

def modal_free : formula → Prop
| □_ := false
| ◇_ := false
| _ := true

def formula.to_prop (asgn : symbol → Prop) : formula → Prop
| ⊤ := true
| ⊥ := false
| (formula.symbol s) := asgn s
| ¬a := ¬a.to_prop
| (a ∧ b) := a.to_prop ∧ b.to_prop
| (a ∨ b) := a.to_prop ∨ b.to_prop
| (a ⟶ b) := a.to_prop → b.to_prop 
| (a ↔ b) := a.to_prop ↔ b.to_prop
| □a := false
| ◇a := false

structure tautology :=
(a : formula)
(modal_free : modal_free a)
(taut : ∀asgn, a.to_prop asgn)

def subst (substs : symbol → formula) : formula → formula
| ⊤ := ⊤
| ⊥ := ⊥
| (formula.symbol s) := substs s
| ¬a := ¬subst a
| (a ∧ b) := subst a ∧ subst b
| (a ∨ b) := subst a ∨ subst b
| (a ⟶ b) := subst a ⟶ subst b
| (a ↔ b) := subst a ↔ subst b
| □a := □subst a
| ◇a := ◇subst a

structure model :=
{world : Type}
(w : set world)
(r : world → world → Prop)
(v : symbol → set world)

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

@[simp] def true_in (m : model) (a : formula) := ∀w ∈ m.w, ⟨m, w⟩ ⊩ a

reserve infix ` ⊩ ` :15
notation m ⊩ a := true_in m a

def substitution_inst (a b : formula) : Prop :=
∃substs, subst substs a = b

def substitution_insts (a : formula) : set formula :=
λb, substitution_inst a b

inductive derivable (axms : set formula) : formula → Prop
| taut (taut : tautology) (a : formula) (h : substitution_inst taut.a a) : derivable a
| axm (axm : formula) {ha : axm ∈ axms} (a : formula) (h : substitution_inst axm a) : derivable a
| mp {a b : formula} (hab : derivable (a ⟶ b)) (ha : derivable a) : derivable b
| nec {a : formula} (ha : derivable a) : derivable □a

reserve prefix `⊢ ` :15
reserve infix ` ⊢ ` :15

notation axms ⊢ a := derivable axms a
notation ⊢ a := λ_, false ⊢ a

-- TODO: should really be a class of models
@[simp] def valid (c : set model) (a : formula) := ∀m ∈ c, m ⊩ a

reserve prefix `⊨ ` :15
reserve infix ` ⊨ ` :15

notation c ⊨ a := valid c a
notation ⊨ a := set.univ ⊨ a

theorem K : ∀(A B : formula), ⊨ □(A ⟶ B) ⟶ (□A ⟶ □B) :=
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

theorem dual : ∀A : formula, ⊨ ◇A ↔ ¬□¬A :=
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

theorem tautology.valid {c : set model} (taut : tautology) (a : formula) : substitution_inst taut.a a → (c ⊨ a) := sorry

theorem mp_valid {c : set model} (a b : formula) : (c ⊨ a ⟶ b) → (c ⊨ a) → (c ⊨ b) := sorry

theorem nec_valid {c : set model} (a : formula) : (c ⊨ a) → (c ⊨ □a) := sorry

theorem soundness (c : set model) (axms : set formula)
    (haxms : ∀axm ∈ axms, ∀a, substitution_inst axm a → (c ⊨ a)) :
  ∀b, (axms ⊢ b) → (c ⊨ b) :=
begin
  intros b hd,
  induction hd,
  { apply tautology.valid hd_taut,
    assumption, },
  { apply haxms hd_axm,
    assumption', },
  { apply mp_valid hd_a hd_b,
    assumption', },
  { apply nec_valid,
    assumption, },
end