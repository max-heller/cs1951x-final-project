import .formula
import .semantics

/-- A logic is a set of axioms. -/
@[reducible]
def logic := set formula

/-- The normal modal logic `K`. -/
def logic.k : set formula := {k 0 1, dual 0}