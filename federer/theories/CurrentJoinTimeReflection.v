(** Federer (1969), 4.1.11, p. 365: the time component
    t maps to 1-t in the original reversing map. These supporting
    laws reuse the scalar-line identification, original affine
    predicate and proved finite-dimensional smoothness. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals ring.
From Federer Require Import Hom AffineMaps RealNormUP NormDifferentialUP
  NormOpenDomainLaws NormRegularity InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct EuclideanOneCoordinate EuclideanAffineSmooth.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [current_join_time_reflection]: the original
    reflection 1-t in the time coordinate of p(x,t,y), Federer
    4.1.11, p. 365. This is existing vector subtraction on R^1. *)
Definition current_join_time_reflection (R:realType) (z:R_n R 1%N):R_n R 1%N:=
  @euclidean_one_embed R 1-z.

(** Source for [current_join_time_reflection_coordinates]: the
    original reflected coordinate is exactly 1-t, supporting the
    reversing map in Federer 4.1.11, p. 365. *)
Lemma current_join_time_reflection_coordinates (R:realType) t:
  current_join_time_reflection (@euclidean_one_embed R t)=@euclidean_one_embed R (1-t).
Proof. apply/ffunP=>i;by rewrite /current_join_time_reflection /euclidean_one_embed !ffunE. Qed.

(** Source for [current_join_time_reflection_affine]: the
    time reflection is an affine map under the original 2.7.16
    definition, supporting Federer 4.1.11, p. 365. *)
Lemma current_join_time_reflection_affine (R:realType):
  is_affine_map (@current_join_time_reflection R).
Proof.
move=>x y a b hab;apply/ffunP=>i.
rewrite /current_join_time_reflection /euclidean_one_embed !ffunE.
change (1-(a*x i+b*y i)=a*(1-x i)+b*(1-y i)).
rewrite -{1}hab;ring.
Qed.

(** Source for [current_join_time_reflection_smooth]: the
    original time reflection is smooth on every open time
    domain, supporting the reversing pushforward of Federer
    4.1.11, p. 365. No stronger domain condition is imposed. *)
Theorem current_join_time_reflection_smooth (R:realType)
    (U:set (R_n R 1%N))
    (hU:forall t,U t->norm_domain_interior
      (inner_norm (@euclidean_inner_productP R 1%N)) U t):
  norm_class_all_orders
    (inner_norm_real_norm (@euclidean_inner_productP R 1%N))
    (inner_norm_real_norm (@euclidean_inner_productP R 1%N)) U
    (@current_join_time_reflection R).
Proof. exact:(@euclidean_affine_map_smooth R 1%N 1%N U hU
  (@current_join_time_reflection R) (@current_join_time_reflection_affine R)). Qed.

(** Source for [current_join_time_reflection_involution]:
    reflecting twice restores the time coordinate, supporting
    the original reversing map in Federer 4.1.11, p. 365. *)
Lemma current_join_time_reflection_involution (R:realType):
  involutive (@current_join_time_reflection R).
Proof.
move=>z;rewrite /current_join_time_reflection opprB addrCA subrr addr0.
reflexivity.
Qed.
