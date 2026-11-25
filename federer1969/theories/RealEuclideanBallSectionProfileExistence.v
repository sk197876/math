(** Federer 2.10.27, p. 191: an existence witness for the
    independently specified pointwise real-degree profile. Its exact
    integral is a separate obligation, not part of this selection. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import EuclideanInnerProduct InnerMetric RealPower
  RealHausdorffBallCoefficient RealEuclideanBallSectionProfileUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [real_euclidean_ball_section_profile_exists]: supporting
    existence of the exact pointwise profile of Federer 2.10.27,
    p. 191. Real powers and the Gamma coefficient are already opaque;
    this witness is later hidden by the independent value signature.
    No integral identity is inferred merely from this existence. *)
Theorem real_euclidean_ball_section_profile_exists (R:realType) m (k:R)
    (hk:(0<=k)%R) (u:inner_metric_space (@euclidean_inner_productP R m)) (r:R):
  exists q,is_real_euclidean_ball_section_profile hk u r q.
Proof.
exists (fun y=>if (mdist u y<=r)%R then
  (real_hausdorff_ball_coefficient hk*real_power (Num.sqrt (r^+2-mdist u y^+2)) k)%R%:E
  else 0);constructor.
- by move=> y hy;rewrite hy.
- move=> y hy;have hn:~~(mdist u y<=r)%R by rewrite -ltNge.
  by rewrite (negbTE hn).
Qed.
