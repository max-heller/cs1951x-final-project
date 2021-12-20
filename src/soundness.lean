import .logics
import .semantics
import .derivations

/-- If all of a modal system `Σ`'s axioms are valid in a set `𝒞` of models, `Σ` is sound with
    respect to `𝒞`. -/
theorem soundness (𝒞 : set model) (axms : set formula)
    (haxms : ∀axm ∈ axms, ∀a, substitution_inst axm a → (𝒞 ⊨ a)) :
  ∀b, (axms ⊢ b) → (𝒞 ⊨ b) :=
begin
  intros b hd,
  induction hd,
  { apply valid_imp_valid_in _,
    apply k.valid, },
  { apply valid_imp_valid_in _,
    apply dual.valid, },
  { apply valid_imp_valid_in _,
    apply tautology.valid,
    assumption, },
  { apply haxms hd_axm,
    assumption', },
  { intros m _ w _,
    apply mp_valid,
    assumption', },
  { apply nec_valid,
    assumption, },
end

/-- A modal system `Σ` is sound with respect to a set `𝒞` of models iff all `Σ`-derivable formulas
    are valid in `𝒞`. -/
class sound (𝒞 : set model) (axms : set formula) :=
(sound : ∀a, (axms ⊢ a) → (𝒞 ⊨ a))

instance logic.k.sound : sound set.univ logic.k :=
{ sound :=
  begin
    intros b hd,
    apply soundness set.univ logic.k,
    { intros axm haxm a ha,
      rw logic.k at haxm,
      cases haxm,
      repeat {
        cases ha with s hs,
        simp at haxm,
        simp [haxm] at hs,
        rw ←hs,
      },
      { apply k.valid, },
      { apply dual.valid, }, },
    { assumption, },
  end }