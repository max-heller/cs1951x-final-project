import .semantics
import .derivations

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