(** Federer (1969), 3.2.28(4), printed p. 267: the explicit
    sqrt(2) ball lifting estimate for T(x)= x^2/2 on a
    unit sphere. The antipodal choice stays local to existence. *)
From mathcomp Require Import all_boot all_order all_algebra reals lra ring.
From Federer Require Import TensorUP Bilinear BilinearNegation InnerProductUP InnerProductLaws
  InnerNorm InnerNormInequalities SymmetricAlgebra SymmetricGrading
  InnerSymmetric InnerSymmetricPositivity SymmetricSquareGeometry.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Section Lifts.
Variable R:realType.
Variable V:lmodType R.
Variable B:V->V->R.
Hypothesis hB:is_inner_product B.
Local Notation N:=(inner_norm hB).
Local Notation T:=(@inner_projective_square R V).
Local Notation hS:=(@symmetric_inner_productP R V B hB 2).
Local Notation NS:=(inner_norm hS).

(** Source for [inner_unit_difference_square]: |x-y|^2= 2-2x.y
    for unit x,y, supporting the final distance formula in
    Federer 3.2.28(4), p. 267. *)
Lemma inner_unit_difference_square x y:
  N x= 1 ->N y= 1 ->N (x-y)^+2= 2-2*B x y.
Proof.
move=>hx hy; rewrite inner_norm_sqr (bilBl (inner_bilinear hB))
  !(bilBr (inner_bilinear hB)) (inner_symmetric hB y x)
  -(inner_norm_sqr hB x) -(inner_norm_sqr hB y) hx hy !expr1n.
by ring.
Qed.

(** Source for [inner_projective_square_positive_lift_bound]:
    the metric estimate after choosing the sign with x.y>=0,
    Federer 3.2.28(4), p. 267. *)
Lemma inner_projective_square_positive_lift_bound x y:
  N x= 1 ->N y= 1 ->0<=B x y ->
  N (y-x)<=Num.sqrt (2:R)*NS (T y-T x).
Proof.
move=>hx hy hp.
have hC:=inner_cauchy hB x y; rewrite hx hy mul1r in hC.
have hle:B x y<=1:=le_trans (ler_norm _) hC.
have hLeft:=inner_norm_nonnegative hB (y-x).
have hRight:=mulr_ge0 (sqrtr_ge0 (2:R)) (inner_norm_nonnegative hS (T y-T x)).
rewrite -(ler_sqr hLeft hRight) exprMn sqr_sqrtr ?ler0n //
  (inner_unit_difference_square hy hx)
  (@inner_projective_square_unit_distance R V B hB y x hy hx)
  (inner_symmetric hB y x).
nra.
Qed.

(** Source for [inner_projective_square_unit_lift]: a unit
    image point lifts within sqrt(2) times its image distance
    by choosing y or -y, Federer 3.2.28(4), p. 267. *)
Theorem inner_projective_square_unit_lift x y:
  N x= 1 ->N y= 1 ->exists z,
    (z= y \/ z= -y) /\ T z= T y /\ N z= 1 /\
    N (z-x)<=Num.sqrt (2:R)*NS (T y-T x).
Proof.
move=>hx hy; case:(leP 0 (B x y))=>hp.
- exists y; split; first by left.
  split=>//; split=>//; exact:inner_projective_square_positive_lift_bound.
- exists (-y); split; first by right.
  split; first exact:(@inner_projective_square_antipodal R V B hB y).
  have hny:N (-y)= 1 by rewrite inner_normN hy.
  split=>//.
  have hPositive:0<=B x (-y).
    by rewrite (bilNr (inner_bilinear hB)) oppr_ge0 ltW.
  have hb:=inner_projective_square_positive_lift_bound hx hny hPositive.
  by rewrite (@inner_projective_square_antipodal R V B hB y) in hb.
Qed.
End Lifts.
