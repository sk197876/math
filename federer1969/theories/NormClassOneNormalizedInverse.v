(** Federer (1969), 3.1.1, p. 210: the normalized inverse-function
    theorem, with f(0)=0 and Df(0)=identity. Quantitative estimates specify
    precisely the neighbourhoods used in the existence proof. *)
From mathcomp Require Import all_boot all_order all_algebra reals topology.
From Federer Require Import Hom RealNormUP NormMetric CompleteMetricUP
  NormClassOneUP NormClassOneIdentityRemainder NearIdentityNormBall.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [norm_class_one_normalized_inverse]: the normalized
    case of the inverse-function argument in Federer 3.1.1, p. 210.
    For each 0<c<1 a closed ball lies in the domain, f is injective there
    with the displayed lower increment bound, and its image contains
    the closed ball of radius (1-c)r. All existence premises come from
    class one and completeness, not an assumed local inverse. *)
Theorem norm_class_one_normalized_inverse (R : realType) (X : lmodType R)
    (N : X -> R) (hN : is_real_norm N)
    (hcomplete : is_complete_metric_space [the metricType R of real_norm_metric_space hN])
    (A : X -> Prop) (f : X -> X) (D : X -> Hom X X) :
  is_norm_class_one_field N N A f D -> A 0 -> f 0 = 0 ->
  (forall v, D 0 v = v) -> forall c : R, 0 < c < 1 ->
  exists r : R, 0 < r /\ (forall x, N x <= r -> A x) /\
    (forall x z, N x <= r -> N z <= r -> (1-c)*N (x-z) <= N (f x-f z)) /\
    (forall x z, N x <= r -> N z <= r -> f x = f z -> x = z) /\
    (forall y, N y <= (1-c)*r -> exists x, N x <= r /\ f x = y).
Proof.
move=> hf hA0 hf0 hD0 c hc.
have [r [hr [hAr hcontract]]] := @norm_class_one_identity_remainder R X N hN A f D
  hf hA0 hD0 c (andP hc).1.
exists r; split=> //; split=> //; split.
- exact: (@near_identity_norm_lower_bound R X N hN f (fun x => N x <= r) c hcontract).
- split.
  + exact: (@near_identity_norm_injective R X N hN f (fun x => N x <= r) c (andP hc).2 hcontract).
  + exact: (@near_identity_norm_ball_surjective R X N hN hcomplete f c r hf0 hc hr hcontract).
Qed.
