(** Federer 2.10.27, p. 191: opaque selection of the original
    real-degree profile. Later integral proofs use only its earlier
    exact value laws, not the pointwise witness's representation. *)
From mathcomp Require Import all_boot all_order all_algebra boolp reals constructive_ereal topology.
From Federer Require Import EuclideanInnerProduct InnerMetric
  RealEuclideanBallSectionProfileUP RealEuclideanBallSectionProfileExistence.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Module Type RealEuclideanBallSectionProfileSignature.
(** Source for [value]: the real-degree cost profile of Federer
    2.10.27, p. 191, after its independent specification and existence. *)
Parameter value:forall (R:realType) m (k:R) (hk:(0<=k)%R),
  inner_metric_space (@euclidean_inner_productP R m)->R->
  inner_metric_space (@euclidean_inner_productP R m)->\bar R.
(** Source for [laws]: the independently stated pointwise inside
    and outside values of the profile in Federer 2.10.27, p. 191. *)
Parameter laws:forall (R:realType) m (k:R) (hk:(0<=k)%R)
  (u:inner_metric_space (@euclidean_inner_productP R m)) (r:R),
  is_real_euclidean_ball_section_profile hk u r (@value R m k hk u r).
End RealEuclideanBallSectionProfileSignature.
Module RealEuclideanBallSectionProfile:RealEuclideanBallSectionProfileSignature.
(** Source for [value]: private choice from the proved profile
    value existence for Federer 2.10.27, p. 191. *)
Definition value (R:realType) m (k:R) (hk:(0<=k)%R)
    (u:inner_metric_space (@euclidean_inner_productP R m)) r:=
  projT1 (cid (@real_euclidean_ball_section_profile_exists R m k hk u r)).
(** Source for [laws]: the selected profile satisfies the original
    independent value laws, Federer 2.10.27, p. 191. *)
Lemma laws (R:realType) m (k:R) (hk:(0<=k)%R)
    (u:inner_metric_space (@euclidean_inner_productP R m)) r:
  is_real_euclidean_ball_section_profile hk u r (@value R m k hk u r).
Proof. exact:projT2 (cid (@real_euclidean_ball_section_profile_exists R m k hk u r)). Qed.
End RealEuclideanBallSectionProfile.
