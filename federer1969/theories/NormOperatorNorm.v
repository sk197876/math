(** Public general operator norm used in Federer (1969), 3.1.1,
    pp. 209–210. These consequences use only its opaque least-bound laws. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import Hom RealNormUP NormDifferentialUP
  NormOperatorNormUP NormOperatorNormSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [norm_operator_norm]: the norm of a continuous linear
    map between the normed spaces of Federer 3.1.1, pp. 209–210. *)
Definition norm_operator_norm (R : realType) (X Y : lmodType R)
    (NX : X -> R) (NY : Y -> R) (hNX : is_real_norm NX)
    (hNY : is_real_norm NY) (L : Hom X Y) (hL : norm_bounded_linear NX NY L) :=
  @NormOperatorNorm.value R X Y NX NY hNX hNY L hL.

(** Source for [norm_operator_norm_specification]: the abstract
    operator-norm laws for Federer 3.1.1, pp. 209–210. *)
Theorem norm_operator_norm_specification (R : realType) (X Y : lmodType R)
    (NX : X -> R) (NY : Y -> R) (hNX : is_real_norm NX)
    (hNY : is_real_norm NY) (L : Hom X Y) (hL : norm_bounded_linear NX NY L) :
  is_norm_operator_norm NX NY L (norm_operator_norm hNX hNY hL).
Proof. exact: NormOperatorNorm.laws. Qed.

(** Source for [norm_operator_norm_independent]: supporting intrinsicness
    of the norm in Federer 3.1.1, pp. 209–210: its value does not depend
    on the proof of boundedness supplied to the sealed interface. *)
Theorem norm_operator_norm_independent (R : realType) (X Y : lmodType R)
    (NX : X -> R) (NY : Y -> R) (hNX : is_real_norm NX)
    (hNY : is_real_norm NY) (L : Hom X Y) (hL hL' : norm_bounded_linear NX NY L) :
  norm_operator_norm hNX hNY hL = norm_operator_norm hNX hNY hL'.
Proof. exact: norm_operator_unique (NormOperatorNorm.laws hNX hNY hL)
  (NormOperatorNorm.laws hNX hNY hL'). Qed.

(** Source for [norm_unit_ball_bound]: supporting normalisation for
    the operator norm in Federer 3.1.1, pp. 209–210. A bound on the
    closed unit ball gives the corresponding homogeneous bound on every
    vector, including zero, without selecting a maximising vector. *)
Lemma norm_unit_ball_bound (R : realType) (X Y : lmodType R)
    (NX : X -> R) (NY : Y -> R) (hNX : is_real_norm NX)
    (hNY : is_real_norm NY) (L : Hom X Y) (C : R) :
  (forall x, NX x <= 1 -> NY (L x) <= C) ->
  0 <= C /\ forall x, NY (L x) <= C*NX x.
Proof.
move=> hC.
have hz : NX 0 <= 1 by rewrite (real_seminorm_zero hNX.1).
have hn := hC 0 hz; rewrite linear0 (real_seminorm_zero hNY.1) in hn.
split=> // x; have [->|hx] := eqVneq x 0.
  by rewrite linear0 (real_seminorm_zero hNY.1) (real_seminorm_zero hNX.1) mulr0.
have hp : 0 < NX x by rewrite (real_norm_positive hNX.1 hNX.2).
have hu : NX ((NX x)^-1 *: x) <= 1.
  by rewrite (real_seminorm_scale hNX.1) normfV (ger0_norm (ltW hp)) mulVf ?gt_eqF.
have hh := hC _ hu.
rewrite linearZ /= (real_seminorm_scale hNY.1)
  normfV (ger0_norm (ltW hp)) mulrC in hh.
by rewrite ler_pdivrMr // in hh.
Qed.

(** Source for [norm_operator_unit_ball_characterisation]: the supremum
    norm used in Federer 3.1.1, pp. 209–210, via the closed-unit-ball
    convention of 1.7.6, p. 33. The least-bound specification is exactly
    the supremum property for image lengths on that ball. This theorem
    does not yet assert the local limsup identity for a differential. *)
Theorem norm_operator_unit_ball_characterisation (R : realType)
    (X Y : lmodType R) (NX : X -> R) (NY : Y -> R)
    (hNX : is_real_norm NX) (hNY : is_real_norm NY) (L : Hom X Y) n :
  is_norm_operator_norm NX NY L n <->
  (forall x, NX x <= 1 -> NY (L x) <= n) /\
  (forall C, (forall x, NX x <= 1 -> NY (L x) <= C) -> n <= C).
Proof.
split.
- move=> hn; split.
  + move=> x hx; apply: le_trans (norm_operator_bound hn x) _.
    have hh := ler_wpM2l (norm_operator_nonnegative hn) hx.
    by rewrite mulr1 in hh.
  + move=> C hC.
    have [hC0 hb] := @norm_unit_ball_bound R X Y NX NY hNX hNY L C hC.
    exact: (norm_operator_least hn hC0 hb).
- move=> [hb hl].
  have [hn hbound] := @norm_unit_ball_bound R X Y NX NY hNX hNY L n hb.
  split=> // C hC hCb; apply: hl=> x hx.
  apply: le_trans (hCb x) _.
  have hh := ler_wpM2l hC hx; by rewrite mulr1 in hh.
Qed.
