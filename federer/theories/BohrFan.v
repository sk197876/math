(** Public finite-fan interface supporting Federer (1969),
    2.8.20, p. 152. Cesari1939 Lemma III, p. 306,
    chooses the fan size using an unbounded harmonic sum.
    This module derives the resulting small-member fraction
    from the sealed fan specification, without unfolding the
    coordinate construction. It supplies the finite group; the complete fine
    rectangle covering is assembled in SmallRectangleMassCover.v.
    Source titles and edition comparisons: VitaliMassObstruction.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals constructive_ereal.
From Federer Require Import BohrFanUP BohrFanSealed HarmonicPrefixBounds ScalarPlaneRectangles.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [bohr_fan]: abstract fan and common core
    supporting Federer 2.8.20, p. 152; Saks1934
    Lemma B, p. 258. The data are exposed only
    through the sealed specification. *)
Definition bohr_fan (R : realType) r (hr : (0 < r)%N) := @BohrFan.value R r hr.

(** Source for [bohr_fan_specification]: the proved laws of
    the fan supporting Federer 2.8.20, p. 152.
    Concrete widths, heights and strips are not unfolded. *)
Lemma bohr_fan_specification (R : realType) r (hr : (0 < r)%N) :
  is_bohr_fan (@bohr_fan R r hr).1 (@bohr_fan R r hr).2.
Proof. exact: BohrFan.laws. Qed.

(** Source for [small_member_bohr_fan_exists]: the small
    equal-area members relative to their union in Saks1934
    (4), p. 258, using the harmonic cutoff of
    Cesari1939 Lemma III, p. 306, supporting Federer
    2.8.20, p. 152. For every positive error eta
    this gives a finite fan all of whose members have area
    strictly less than eta times the area of their union. *)
Theorem small_member_bohr_fan_exists (R : realType) (eta : R) :
  (0 < eta)%R -> exists (r : nat) (F : 'I_r -> set (R*R)) E,
    is_bohr_fan F E /\ forall i,
      scalar_plane_lebesgue (F i) < eta%:E * scalar_plane_lebesgue (\bigcup_(j in @setT 'I_r) F j).
Proof.
move=> heta.
have [r [hr hH]] := @harmonic_partial_sums_unbounded R (eta^-1)%R.
pose w := @bohr_fan R r hr.
have hf := @bohr_fan_specification R r hr.
have hrR : (0 < r%:R :> R)%R by rewrite ltr0n.
have hinv : (0 < (r%:R : R)^-1)%R by rewrite invr_gt0.
have hgain : (1 < eta * harmonic_partial_sum R r)%R.
  have hdiv : (1/eta < harmonic_partial_sum R r)%R by rewrite mul1r.
  move: hdiv; rewrite ltr_pdivrMr //; by rewrite mulrC.
have hscalar : ((r%:R : R)^-1 < eta * (harmonic_partial_sum R r / r%:R))%R.
  have hm : (1 * (r%:R : R)^-1 < (eta * harmonic_partial_sum R r) * (r%:R : R)^-1)%R.
    by rewrite ltr_pM2r.
  by move: hm; rewrite mul1r -mulrA.
exists r,w.1,w.2; split; first exact hf.
move=> i; rewrite (@bohr_fan_equal_area R r w.1 w.2 hf i).
have hb : eta%:E * (harmonic_partial_sum R r / r%:R)%:E <=
    eta%:E * scalar_plane_lebesgue (\bigcup_(j in @setT 'I_r) w.1 j).
  apply: lee_wpmul2l; first by rewrite lee_fin; exact: ltW heta.
  exact: bohr_fan_harmonic_gain hf.
apply: lt_le_trans _ hb; by rewrite -EFinM lte_fin.
Qed.
