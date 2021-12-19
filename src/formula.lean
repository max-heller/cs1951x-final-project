import tactic.alias
import tactic.basic
import tactic.linarith

@[reducible]
def symbol := ℕ

/-- Representation of formulas in modal logic. -/
@[derive decidable_eq]
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

-- Used to construct formulas containing arbitrary symbols e.g. `0 ∨ 1` (`p ∨ q`).
instance formula.has_zero : has_zero formula := { zero := formula.symbol 0 }
instance formula.has_one : has_one formula := { one := formula.symbol 1 }
instance formula.has_add : has_add formula := {
  add := λx y, match (x, y) with
  | (formula.symbol x, formula.symbol y) := formula.symbol (x + y)
  | (x, _) := x
  end
}

/-- A formula is modal free iff it contains no modal operators. -/
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

/-- Substitutes sentence symbols for formulas in a formula according to a mapping function. -/
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

@[simp] lemma subst.ident (a : formula) : subst formula.symbol a = a :=
begin
  induction a,
  repeat { simp [a_ih, subst] },
  repeat { simp },
  repeat { tauto },
end

@[simp] def substitution_inst (a b : formula) : Prop :=
∃substs, subst substs a = b