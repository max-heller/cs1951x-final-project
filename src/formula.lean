import tactic.alias

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

@[simp] def substitution_inst (a b : formula) : Prop :=
∃substs, subst substs a = b