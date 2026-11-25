(** Federer 2.10.27, p. 191: the real profile agrees with
    the already proved natural-degree profile on every original
    radius and point. Reuse this connection for degree zero. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import EuclideanInnerProduct InnerMetric EuclideanBallVolume RealPower
  RealPowerNaturalHausdorff RealHausdorffBallCoefficient EuclideanBallSectionProfileUP
  RealEuclideanBallSectionProfileUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [real_ball_section_profile_natural_laws]: the
    missing natural-to-real connection for the original ball-section
    profile of Federer 2.10.27, p. 191. It uses the actual Gamma
    coefficient identity and the existing real-power/natural-power
    equality, not a newly assigned coefficient. *)
Lemma real_ball_section_profile_natural_laws (R:realType) m k
    (hk:(0<=(k%:R:R))%R) (u:inner_metric_space (@euclidean_inner_productP R m)) r q:
  is_euclidean_ball_section_profile k u r q ->
  is_real_euclidean_ball_section_profile hk u r q.
Proof.
move=> hq;constructor.
- move=> y hy;rewrite real_hausdorff_ball_coefficient_natural
    real_power_natural_exponent ?sqrtr_ge0 //.
  exact (@ball_section_profile_inside R m k u r q hq y hy).
- exact (@ball_section_profile_outside R m k u r q hq).
Qed.
