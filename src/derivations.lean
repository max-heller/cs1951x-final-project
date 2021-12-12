import .formula
import .semantics
import .tactics

inductive derivable (axms : set formula) : formula → Prop
| k (a b : formula) : derivable (k a b)
| dual (a : formula) : derivable (dual a)
| taut (taut : tautology) (a : formula) (h : substitution_inst taut.a a) : derivable a
| axm (axm ∈ axms) (a : formula) (h : substitution_inst axm a) : derivable a
| mp (a b : formula) (hab : derivable (a ⟶ b)) (ha : derivable a) : derivable b
| nec {a : formula} (ha : derivable a) : derivable □a

reserve prefix `⊢ ` :15
reserve infix ` ⊢ ` :15

notation axms ⊢ a := derivable axms a
notation ⊢ a := ∅ ⊢ a

-- TODO: should be able to infer tautology if formula to prove is modal-free
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