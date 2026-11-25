(** General normed-space background supporting Federer (1969),
    4.1.14, p. 371: extend the bounded linear image map from the
    dense original normal currents to the complete flat space.
    These independent laws specify the extension; no extension
    existence is assumed. Completeness is needed only in the target. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import Hom.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [is_bounded_dense_linear_extension]: the agreement
    and original finite flat-norm bound retained when extending the
    linear operator in Federer 4.1.14, p. 371. The source module A
    need not carry a norm, and the inclusion need not be injective. *)
Definition is_bounded_dense_linear_extension (R:realType)
    (A V W:lmodType R) (NV:V->R) (NW:W->R)
    (i:Hom A V) (F:Hom A W) (C:R) (G:Hom V W):Prop:=
  (forall a,G (i a)=F a) /\ (forall v,NW (G v)<=C*NV v).

(** Source for [is_norm_dense_linear_image]: the epsilon form of
    density of the original normal subspace for the flat norm,
    used in Federer 4.1.14, p. 371. It assumes no completeness
    of either source module. *)
Definition is_norm_dense_linear_image (R:realType)
    (A V:lmodType R) (NV:V->R) (i:Hom A V):Prop:=
  forall (v:V) (epsilon:R),0<epsilon->exists a,NV (v-i a)<epsilon.
