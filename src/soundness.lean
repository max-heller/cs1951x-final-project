import .logics
import .semantics
import .derivations

/-- If all of a modal system `Î£`'s axioms are valid in a set `ð` of models, `Î£` is sound with
    respect to `ð`. -/
theorem soundness (ð : set model) (axms : set formula)
    (haxms : âaxm â axms, âa, substitution_inst axm a â (ð â¨ a)) :
  âb, (axms â¢ b) â (ð â¨ b) :=
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

/-- A modal system `Î£` is sound with respect to a set `ð` of models iff all `Î£`-derivable formulas
    are valid in `ð`. -/
class sound (ð : set model) (axms : set formula) :=
(sound : âa, (axms â¢ a) â (ð â¨ a))

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
        rw âhs,
      },
      { apply k.valid, },
      { apply dual.valid, }, },
    { assumption, },
  end }