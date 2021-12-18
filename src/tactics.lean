import tactic.basic

import .formula

@[simp] def p := formula.symbol 0
@[simp] def q := formula.symbol 1
@[simp] def r := formula.symbol 2

meta def build_func : pexpr → expr → tactic pexpr
| f `(and %%l %%r) :=
  do
    f ← build_func f l,
    build_func f r
| f `(%%a = %%b) :=
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
| f _ := return f

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