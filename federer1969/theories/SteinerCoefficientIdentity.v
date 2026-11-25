(** Federer (1969), 3.2.35, p. 272:
    the exact coefficient evaluation at the end
    of the dimension induction, with every
    divisor proved positive. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp constructive_ereal lra ring.
From Federer Require Import ProjectionBeta ProjectionBetaRatio SteinerProjectionBetaProduct
  UnitBallIntrinsicVolume EuclideanBallVolume.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [steiner_coefficient_product_identity]:
    the last scalar equality in Federer 3.2.35,
    p. 272, with n=m+j+1. The proved
    beta product comes from the actual Gamma
    formula of 3.2.13, p. 251. Cauchy's
    actual unit-ball identity and 3.2.13's
    sphere mass supply the alpha normalization.
    Both m=0 and j=0 are retained; no
    coefficient law or Steiner theorem is assumed. *)
Lemma steiner_coefficient_product_identity (R:realType) m j:
  2*euclidean_unit_ball_volume R j*
    @projection_beta R (m+j).+1 m (projection_offset_guard m j) 1=
  j.+1%:R*euclidean_unit_ball_volume R j.+1*
    @projection_beta R (m+j) m (leq_addr j m) 1*
    @projection_beta R (m+j).+1 (m+j) (leqnSn (m+j)) 1.
Proof.
have hAlpha:=unit_ball_cauchy_coefficient R j.
have hBeta:=steiner_projection_beta_product R m j.
have hScaled:=congr1 (fun v:R=>v* @projection_beta R (m+j).+1 m (projection_offset_guard m j) 1) hAlpha.
have hProduct:=congr1 (fun v:R=>j.+1%:R*euclidean_unit_ball_volume R j.+1*v) hBeta.
nra.
Qed.

(** Source for [steiner_coefficient_quotient_identity]:
    the normalized coefficient evaluation in
    Federer 3.2.35, p. 272. The positive
    natural radius exponent and both existing
    positive projection constants justify the
    division, including the zeroth and full
    induction degrees. *)
Lemma steiner_coefficient_quotient_identity (R:realType) m j:
  (2*euclidean_unit_ball_volume R j*
    @projection_beta R (m+j).+1 m (projection_offset_guard m j) 1)/
  (j.+1%:R* @projection_beta R (m+j) m (leq_addr j m) 1*
    @projection_beta R (m+j).+1 (m+j) (leqnSn (m+j)) 1)=
  euclidean_unit_ball_volume R j.+1.
Proof.
pose D:R:=j.+1%:R* @projection_beta R (m+j) m (leq_addr j m) 1*
  @projection_beta R (m+j).+1 (m+j) (leqnSn (m+j)) 1.
have hDPositive:0<D.
  rewrite /D; apply:mulr_gt0.
  - apply:mulr_gt0; first by rewrite ltr0n.
    exact:(@projection_beta_positive R (m+j) m (leq_addr j m) 1 (lexx 1)).
  - exact:(@projection_beta_positive R (m+j).+1 (m+j) (leqnSn (m+j)) 1 (lexx 1)).
have hDNonzero:D!=0 by rewrite gt_eqF.
have hProduct:=steiner_coefficient_product_identity R m j.
have hNumerator:2*euclidean_unit_ball_volume R j*
    @projection_beta R (m+j).+1 m (projection_offset_guard m j) 1=
    euclidean_unit_ball_volume R j.+1*D by rewrite hProduct /D; ring.
change ((2*euclidean_unit_ball_volume R j*
  @projection_beta R (m+j).+1 m (projection_offset_guard m j) 1)/D=euclidean_unit_ball_volume R j.+1).
by rewrite hNumerator mulfK.
Qed.
