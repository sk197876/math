(** Federer (1969), 2.4.15, equality statement p. 89: equality in each
    normalised Holder comparison yields a constant proportion between an
    input norm and the sum norm. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import RealPower RealPowerDivision.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [minkowski_normalised_power_proportion]: supporting
    scalar root cancellation for the equality condition in
    Federer 2.4.15, p. 89. The two normalising
    norms are positive; the pointwise norms may be zero.
    The relation rq=p includes r=p-1 and q=p/(p-1). *)
Lemma minkowski_normalised_power_proportion (R : realType) (p q r a c s t : R) :
  0 < p -> 0 < q -> 0 < r -> r*q=p ->
  0 < a -> 0 < c -> 0 <= s -> 0 <= t ->
  real_power (a^-1*s) p = real_power ((real_power c r)^-1*real_power t r) q ->
  s = (a/c)*t.
Proof.
move=> hp hq hr hrq ha hc hs ht he.
have hai : 0 <= a^-1 by rewrite invr_ge0; exact: ltW ha.
have hci : 0 <= c^-1 by rewrite invr_ge0; exact: ltW hc.
have hbasea : 0 <= a^-1*s := mulr_ge0 hai hs.
have hbasec : 0 <= c^-1*t := mulr_ge0 hci ht.
have hweight : (real_power c r)^-1*real_power t r = real_power (c^-1*t) r.
  by rewrite (@real_power_product R c^-1 t r hci ht) (@real_power_inverse_base R c r hc).
rewrite hweight (@real_power_positive_iterate R (c^-1*t) r q hbasec hr hq) hrq in he.
have hroot := congr1 (fun z => real_power z p^-1) he.
rewrite (@real_power_root_cancel R (a^-1*s) p hbasea hp)
  (@real_power_root_cancel R (c^-1*t) p hbasec hp) in hroot.
have hh := congr1 (fun z => a*z) hroot.
by rewrite !mulrA mulfV ?gt_eqF // mul1r in hh.
Qed.
