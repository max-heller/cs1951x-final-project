import tactic.alias
import tactic.suggest
import tactic.basic
import tactic.interactive

alias string ← symbol

inductive formula : Type
| bottom : formula
| top : formula
| symbol (s : symbol) : formula
| not (a : formula) : formula
| and (a b : formula) : formula
| or (a b : formula) : formula
| implies (a b : formula) : formula
| iff (a b : formula) : formula
| box (a : formula) : formula
| diamond (a : formula) : formula

reserve infixr ` ⟶ ` :(std.prec.arrow+1)
reserve prefix `□` :40
reserve prefix `◇` :40

notation `⊥` := formula.bottom
notation `⊤` := formula.top
notation ¬ a := formula.not a
notation a ` ∧ ` b := (formula.and a b)
notation a ` ∨ ` b := formula.or a b
notation a ` ⟶ ` b := formula.implies a b
notation a ` ↔ ` b := formula.iff a b
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

meta def formula.to_pexpr : formula → pexpr
| ⊤ := ``(⊤)
| ⊥ := ``(⊥)
| (formula.symbol s) := ``(formula.symbol %%s)
| ¬a := ``(¬%%a.to_pexpr)
| (a ∧ b) := ``(%%a.to_pexpr ∧ %%b.to_pexpr)
| (a ∨ b) := ``(%%a.to_pexpr ∨ %%b.to_pexpr)
| (a ⟶ b) := ``(%%a.to_pexpr ⟶ %%b.to_pexpr)
| (a ↔ b) := ``(%%a.to_pexpr ↔ %%b.to_pexpr)
| □a := ``(□%%a.to_pexpr)
| ◇a := ``(◇%%a.to_pexpr)

meta instance formula.has_to_pexpr : has_to_pexpr formula :=
{ to_pexpr := formula.to_pexpr }

@[simp] def modal_free : formula → Prop
| ⊤ := true
| ⊥ := true
| (formula.symbol _) := true
| ¬a := modal_free a
| (a ∧ b) := modal_free a ∧ modal_free b
| (a ∨ b) := modal_free a ∧ modal_free b
| (a ⟶ b) := modal_free a ∧ modal_free b
| (a ↔ b) := modal_free a ∧ modal_free b
| □_ := false
| ◇_ := false

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

structure tautology :=
(a : formula)
{modal_free : modal_free a}
(taut : ∀asgn, satisfies asgn a)

@[simp] def subst (substs : symbol → formula) : formula → formula
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

@[simp] def substitution_inst (a b : formula) : Prop :=
∃substs, subst substs a = b

def substitution_insts (a : formula) : set formula :=
λb, substitution_inst a b

-- TODO: should really be a class of models
@[simp] def valid (c : set model) (a : formula) := ∀m ∈ c, m ⊩ a

reserve prefix `⊨ ` :15
reserve infix ` ⊨ ` :15

notation c ⊨ a := valid c a
notation ⊨ a := set.univ ⊨ a

@[simp] lemma valid_imp_valid_in (a : formula) {ha : ⊨ a} {c : set model} : c ⊨ a :=
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

theorem tautology.valid (taut : tautology) (a : formula) :
  substitution_inst taut.a a → ⊨ a :=
begin
  contrapose,
  intros h₁ h₂,
  simp at h₁,
  apply exists.elim h₁,
  intros m hm,
  cases hm,
  apply exists.elim hm_right,
  intros w hw,
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

theorem mp_valid {c : set model} (a b : formula) : (c ⊨ a ⟶ b) → (c ⊨ a) → (c ⊨ b) :=
begin
  intros hab ha m _ w _,
  apply mp,
  assumption',
  apply hab,
  assumption',
  apply ha,
  assumption',
end

theorem nec_valid {c : set model} (a : formula) : (c ⊨ a) → (c ⊨ □a) :=
begin
  intro ha,
  intros m _ w _,
  intros w' _ hww',
  apply ha,
  assumption',
end

inductive derivable (axms : set formula) : formula → Prop
| k (a b : formula) : derivable (k a b)
| dual (a : formula) : derivable (dual a)
| taut (taut : tautology) (a : formula) (h : substitution_inst taut.a a) : derivable a
| axm (axm : formula) {ha : axm ∈ axms} (a : formula) (h : substitution_inst axm a) : derivable a
| mp (a b : formula) (hab : derivable (a ⟶ b)) (ha : derivable a) : derivable b
| nec {a : formula} (ha : derivable a) : derivable □a

reserve prefix `⊢ ` :15
reserve infix ` ⊢ ` :15

notation axms ⊢ a := derivable axms a
notation ⊢ a := ∅ ⊢ a

theorem soundness (c : set model) (axms : set formula)
    (haxms : ∀axm ∈ axms, ∀a, substitution_inst axm a → (c ⊨ a)) :
  ∀b, (axms ⊢ b) → (c ⊨ b) :=
begin
  intros b hd,
  induction hd,
  { apply valid_imp_valid_in _,
    apply k.valid, },
  { apply valid_imp_valid_in _,
    apply dual.valid, },
  { apply valid_imp_valid_in _,
    apply tautology.valid hd_taut,
    assumption, },
  { apply haxms hd_axm,
    assumption', },
  { intros m _ w _,
    apply mp_valid,
    assumption', },
  { apply nec_valid,
    assumption, },
end

@[simp] def p := formula.symbol "p"
@[simp] def q := formula.symbol "q"
@[simp] def r := formula.symbol "r"

meta def build_func : pexpr → expr → tactic pexpr
| f t :=
  do
    match t with
    | `(and %%l %%r) :=
      do
        f ← build_func f l,
        build_func f r
    | `(%%a = %%b) :=
      match a with
        | expr.app _ a :=
          do 
            t ← tactic.infer_type a,
            match t with
            | `(string) := return ``(λx : symbol, if (x = %%a) then %%b else %%f x)
            | _ := return f
            end
        | _ := return f
      end
    | _ := return f
    end

meta def tactic.substitution_inst : tactic unit :=
do
  tactic.applyc `exists.intro,
  t ← tactic.target,
  f ← build_func ``(λ_, ⊥) t >>= tactic.to_expr,
  tactic.rotate 1,
  tactic.exact f,
  `[tautology!]

meta def tactic.derive_taut (taut : formula) : tactic unit :=
do
  let opts : tactic.apply_cfg := {new_goals := tactic.new_goals.all},
  tactic.applyc `derivable.taut opts,
  tactic.constructor opts,
  taut ← tactic.to_expr taut.to_pexpr,
  tactic.exact taut,
  `[simp only [modal_free]],
  `[tautology!],
  `[simp only [satisfies]],
  `[tautology!],
  `[simp only [substitution_inst, subst]],
  tactic.substitution_inst

example (a b : formula) : ⊢ (a ∨ ¬a) ∧ (b ∨ ¬b) :=
by tactic.derive_taut ((p ∨ ¬p) ∧ (q ∨ ¬q))

example (a b c : formula) : ⊢ (a ⟶ b) ⟶ (b ⟶ c) ⟶ (a ⟶ c) :=
by tactic.derive_taut ((p ⟶ q) ⟶ (q ⟶ r) ⟶ (p ⟶ r))

lemma box_and (a b : formula) : ⊢ □(a ∧ b) ⟶ (□a ∧ □b) :=
begin
  apply derivable.mp,
  { apply derivable.mp,
    { tactic.derive_taut ((p ⟶ q) ⟶ (p ⟶ r) ⟶ p ⟶ (q ∧ r)), },
    { apply derivable.mp,
      { apply derivable.k (a ∧ b) a, },
      { apply derivable.nec,
        tactic.derive_taut (p ∧ q ⟶ p), } } },
  { apply derivable.mp,
    { apply derivable.k, },
    { apply derivable.nec,
      tactic.derive_taut (p ∧ q ⟶ q) } },
end