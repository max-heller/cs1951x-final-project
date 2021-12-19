import .formula

/-- Determines the number of logical and modal connectives in a formula. -/
def formula.size : formula → ℕ
| ⊤ := 0
| ⊥ := 0
| (formula.symbol s) := 0
| ¬a := a.size + 1
| (a ∧ b) := a.size + b.size + 1
| (a ∨ b) := a.size + b.size + 1
| (a ⟶ b) := a.size + b.size + 1
| (a ↔ b) := a.size + b.size + 1
| □a := a.size + 1
| ◇a := a.size + 1

/-- Determines the largest symbol contained in a formula. -/
def formula.max_sym : formula → ℕ
| ⊤ := 0
| ⊥ := 0
| (formula.symbol s) := s
| ¬a := a.max_sym
| (a ∧ b) := (max a.max_sym b.max_sym)
| (a ∨ b) := (max a.max_sym b.max_sym)
| (a ⟶ b) := (max a.max_sym b.max_sym)
| (a ↔ b) := (max a.max_sym b.max_sym)
| □a := a.max_sym
| ◇a := a.max_sym

/-- `build vars n` contains all of the formulas of size `n` using only the variables in `vars`. -/
def build (vars : list ℕ) : ℕ → list formula
| 0 := ⊥ :: ⊤ :: vars.map formula.symbol
| (n + 1) :=
  let xs := build n in
  list.join [
    xs,
    list.join (xs.map (λa, [¬a, □a, ◇a])),
    list.join (xs.map (λa, list.join (xs.map (λb, [a ∧ b, a ∨ b, a ⟶ b, a ↔ b]))))
  ]

lemma build.nonempty (vars : list ℕ) (n : ℕ) : (build vars n).length > 0 :=
begin
  induction n; simp [build],
  apply nat.add_pos_left,
  exact n_ih,
end

lemma build.monotonic {vars vars' : list ℕ} {m n : ℕ} {hv : vars ⊆ vars'} {hmn : m ≤ n} :
  build vars m ⊆ build vars' n :=
sorry

/-- `enumerateₙ n` enumerate all formulas of size `n` with max symbol `n`. -/
def enumerateₙ (stage : ℕ) : list formula := build (list.range (stage + 1)) stage

lemma enumerateₙ.nonempty (n : ℕ) : (enumerateₙ n).length > 0 :=
begin
  rw enumerateₙ,
  induction n; simp [build.nonempty],
end

def enumerateₙ.complete (n : ℕ) (a : formula) : a.max_sym ≤ n ∧ a.size ≤ n → a ∈ enumerateₙ n :=
begin
  intro ha,
  cases ha with hm hs,
  rw enumerateₙ,
  induction n; cases a; simp [formula.size, formula.max_sym, hm, hs, build] at *,
  assumption',
  repeat { apply build.monotonic n_ih,
    simp [list.range_subset], },
  { apply @build.monotonic (list.range (n_n + 2)) _ 0 _,
    { simp [list.range_subset], },
    { linarith, },
    { rw build,
      simp [hm, nat.lt_succ_iff], }, },
  repeat { sorry, },
end

lemma sub_pos_lt {n m : ℕ} (hm : m > 0) : n + 1 - m < n + 1 :=
begin
  have hm' : m ≥ 1 := nat.succ_le_iff.mpr hm,
  calc n + 1 = n + 1 : by refl
         ... > n + (1 - 1) : by simp [nat.add_lt_add_right]
         ... ≥ n + 1 - m : tsub_le_tsub_left hm' (n + 1)
end

/-- `enumerate' n m` is the `n`th formula from the start of the `m`th stage of the enumeration. -/
def enumerate' : ℕ → ℕ → formula
| 0 stage :=
  match enumerateₙ stage with
  | list.nil := ⊥
  | (x :: xs) := x
  end
| (n + 1) stage :=
  let xs := enumerateₙ stage in
  match xs.nth (n + 1) with
  | (some x) := x
  | none :=
    have n + 1 - (enumerateₙ stage).length < n + 1 := sub_pos_lt (enumerateₙ.nonempty stage),
    enumerate' (n + 1 - xs.length) (stage + 1)
  end

def enumerate'.complete (a : formula) : ∃n stage, enumerate' n stage = a :=
sorry

/-- Enumerates all possible formulas. -/
def enumerate (n : ℕ) : formula :=
enumerate' n 0

def enumerate.complete : ∀a, ∃n, enumerate n = a :=
begin
  intro a,
  apply exists.elim (enumerate'.complete a),
  intros n hs,
  cases hs with stage h,
  apply exists.intro ((list.map (λs, (enumerateₙ s).length) (list.range stage)).sum + n),
  rw enumerate,
  induction n with n' ih,
  { simp [enumerate', h], sorry },
  { sorry }
end