(** Federer 2.10.27, p. 191: pointwise finite values of the
    original real-degree ball-section cost. These follow from the
    independent value specification before any integration. *)
From mathcomp Require Import all_boot all_order all_algebra reals constructive_ereal topology.
From Federer Require Import EuclideanInnerProduct InnerMetric RealEuclideanBallSectionProfileUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [real_ball_section_profile_finite]: supporting
    scalar representative for the first display in Federer
    2.10.27, p. 191. Every original profile value is finite,
    including the zero-degree boundary and zero-radius sections. *)
Lemma real_ball_section_profile_finite (R:realType) m (k:R) (hk:0<=k)
    (u:inner_metric_space (@euclidean_inner_productP R m)) r q:
  is_real_euclidean_ball_section_profile hk u r q ->forall y,q y \is a fin_num.
Proof.
move=> hq y;case:(leP (mdist u y) r)=>hy.
- by rewrite (real_ball_section_profile_inside hq hy) fin_numE.
- by rewrite (real_ball_section_profile_outside hq hy) fin_numE.
Qed.
