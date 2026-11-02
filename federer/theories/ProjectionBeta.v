(** Public normalization beta_t(n,m) for Federer (1969), 2.10.5, p. 172. The
    value is specified by the projection integral of 2.7.16(6), pp. 139–140;
    its private witness is opaque. Source context:
    ProjectionBetaConstruction.v. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets
  reals constructive_ereal.
From Federer Require Import ExteriorDiameterUP OrthogonalProjectionConstants ProjectionConstantNorms
  ProjectionBetaSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ereal_scope.

(** Source for [projection_beta]: the beta_t(n,m)
    in the gauge definition of Federer 2.10.5,
    p. 172, with its original universal specification. *)
Definition projection_beta (R : realType) (n m : nat) (hmn : (m<=n)%N)
    (t : \bar R) := @ProjectionBeta.value R n m hmn t.

(** Source for [projection_beta_specification]: the
    defining projection-norm formula of Federer
    2.7.16(6), pp. 139–140, for the constant
    used in 2.10.5, p. 172. *)
Lemma projection_beta_specification (R : realType) (n m : nat) (hmn : (m<=n)%N)
    (t : \bar R) (ht : 1<=t) :
  is_extended_projection_constant (real_exterior_two_nonzero R) t n m
    (@projection_beta R n m hmn t).
Proof. exact: ProjectionBeta.laws. Qed.

(** Source for [projection_beta_positive]: positivity
    of beta_t in Federer 2.7.16(6), p. 139,
    justifying its use as a divisor in 2.10.5,
    p. 172; beta at infinity is one. *)
Lemma projection_beta_positive (R : realType) (n m : nat) (hmn : (m<=n)%N)
    (t : \bar R) (ht : 1<=t) :
  (0<@projection_beta R n m hmn t)%R.
Proof.
have hb := @projection_beta_specification R n m hmn t ht.
case: t ht hb=> [p| |] ht hb //.
- exact: hb.1.
- by rewrite hb ltr01.
Qed.

(** Source for [projection_beta_infinity]: direct
    beta_infinity(n,m)=1 in Federer 2.7.16(6),
    p. 140, for 2.10.5, p. 172. *)
Lemma projection_beta_infinity (R : realType) (n m : nat) (hmn : (m<=n)%N) :
  @projection_beta R n m hmn +oo = 1%R.
Proof. exact: (@projection_beta_specification R n m hmn +oo (leey 1)). Qed.
