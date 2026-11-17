(** Federer 2.10.2, p. 171: the printed alpha(p) for nonnegative real
    p, used in the original coefficients of 2.10.27 and 2.10.45,
    pp. 190-191 and 202-203. Its Gamma equation precedes its value.
    This scalar definition uses the existing opaque Gamma and power laws. *)
From mathcomp Require Import all_boot all_order all_algebra reals ring.
From Federer Require Import EulerGamma EulerGammaHalfParameters
  RealHausdorffNormalisation RealPower RealPowerSuccessor RealPowerNaturalHausdorff
  EuclideanBallVolume HausdorffDiameterCost.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [is_real_hausdorff_ball_coefficient]: the defining
    alpha(p)=Gamma(1/2)^p/Gamma(p/2+1) in Federer 2.10.2, p. 171.
    No Gamma evaluation outside its positive domain is introduced. *)
Definition is_real_hausdorff_ball_coefficient (R : realType) (p : R)
    (hp : 0 <= p) (a : R) : Prop :=
  a = real_power (euler_gamma_half R) p/euler_gamma (real_dimension_gamma_parameter hp).

(** Source for [real_hausdorff_ball_coefficient]: the original real
    alpha(p) from Federer 2.10.2, p. 171. This is the printed scalar
    expression, independent of any covering construction. *)
Definition real_hausdorff_ball_coefficient (R : realType) (p : R)
    (hp : 0 <= p) : R :=
  real_power (euler_gamma_half R) p/euler_gamma (real_dimension_gamma_parameter hp).

(** Source for [real_hausdorff_ball_coefficient_specification]: the
    actual Gamma equation defining alpha(p), Federer 2.10.2, p. 171. *)
Lemma real_hausdorff_ball_coefficient_specification (R : realType) (p : R)
    (hp : 0 <= p) :
  is_real_hausdorff_ball_coefficient hp (real_hausdorff_ball_coefficient hp).
Proof. by []. Qed.

(** Source for [real_hausdorff_ball_coefficient_positive]: supporting
    positivity of every original real alpha(p), Federer 2.10.2, p. 171,
    including p=0. The defining Gamma values are positive. *)
Lemma real_hausdorff_ball_coefficient_positive (R : realType) (p : R)
    (hp : 0 <= p) : 0 < real_hausdorff_ball_coefficient hp.
Proof.
rewrite /real_hausdorff_ball_coefficient; apply: divr_gt0;
  last exact: euler_gamma_positive.
apply: real_power_strictly_positive; exact: euler_gamma_positive.
Qed.

(** Source for [real_hausdorff_ball_coefficient_cost]: the relation
    alpha(p)=2^p times the diameter coefficient in Federer 2.10.2,
    p. 171. This connects the printed product constants to the
    independently specified actual covering measures. *)
Lemma real_hausdorff_ball_coefficient_cost (R : realType) (p : R)
    (hp : 0 <= p) :
  real_hausdorff_normalisation hp*real_power 2 p = real_hausdorff_ball_coefficient hp.
Proof.
rewrite /real_hausdorff_normalisation /real_hausdorff_ball_coefficient divfK //.
apply: lt0r_neq0; apply: real_power_strictly_positive; by rewrite ltr0n.
Qed.

(** Source for [real_hausdorff_ball_coefficient_natural]: the equality
    of real alpha(m) and the original Euclidean unit-ball volume at
    every natural m, Federer 2.10.2, p. 171, referring to 3.2.13,
    p. 251. Include dimension zero. *)
Lemma real_hausdorff_ball_coefficient_natural (R : realType) m
    (hm : (0 <= m%:R :> R)) :
  real_hausdorff_ball_coefficient hm = euclidean_unit_ball_volume R m.
Proof.
rewrite -real_hausdorff_ball_coefficient_cost real_hausdorff_normalisation_natural
  real_power_natural_exponent ?ler0n // /hausdorff_normalisation divfK //.
by rewrite expf_neq0 // pnatr_eq0.
Qed.
