(** Supporting bounds for Federer (1969), 4.1.15,
    p. 372. They use only the original value laws of
    Psi_r, preserving the boundary and zero vector. *)
From mathcomp Require Import all_boot all_order all_algebra
  classical_sets reals ring.
From Federer Require Import RealNormUP InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct RadialShrinkMapUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

Section RadialShrinkMapDisplacement.
Variable R : realType.
Variable n : nat.
Local Notation X := (R_n R n).
Local Notation N :=
  (inner_norm (@euclidean_inner_productP R n)).
Local Notation hN :=
  (inner_norm_real_norm (@euclidean_inner_productP R n)).
Variable r : R.
Hypothesis hr : 0 < r.
Variable P : X -> X.
Hypothesis hP : is_radial_shrink_map r P.

(** Source for [radial_shrink_closed_inner]: Psi_r(y)=0
    also on |y|=r, by the second defining formula in
    Federer 4.1.15, p. 372. This is the closed threshold
    used in the printed agreement assertion for G_r. *)
Theorem radial_shrink_closed_inner y :
  N y <= r -> P y = 0.
Proof.
move=> hy; case: (ltP (N y) r) => hCase.
- exact:(@radial_shrink_inner R n r P hP y hCase).
- have hEqual : N y = r by apply/le_anti; rewrite hy hCase.
  rewrite (@radial_shrink_outer R n r P hP y hCase) hEqual.
  by rewrite divff ?gt_eqF // subrr scale0r.
Qed.

(** Source for [radial_shrink_outer_displacement]: the
    printed radial formula gives exact displacement r
    outside the ball, supporting |Psi_r(y)-y|<=r in
    Federer 4.1.15, p. 372. *)
Theorem radial_shrink_outer_displacement y :
  r <= N y -> N (P y-y) = r.
Proof.
move=> hy.
have hPositive : 0 < N y := lt_le_trans hr hy.
have hDivision : 0 <= r/N y := divr_ge0 (ltW hr) (ltW hPositive).
have hVector : P y-y = -(r/N y) *: y.
  rewrite (@radial_shrink_outer R n r P hP y hy).
  have hSubtract:(1-r/N y)*:y-y=((1-r/N y)-1)*:y.
    by rewrite [RHS]scalerBl scale1r.
  rewrite hSubtract.
  congr (_ *: y); ring.
rewrite hVector (real_seminorm_scale hN.1) normrN
  (ger0_norm hDivision).
by rewrite divfK ?gt_eqF.
Qed.

(** Source for [radial_shrink_displacement_bound]: the
    original |Psi_r(y)-y|<=r for all y, Federer
    4.1.15, p. 372. Dimension zero is included. *)
Theorem radial_shrink_displacement_bound y :
  N (P y-y) <= r.
Proof.
case: (ltP (N y) r) => hy.
- rewrite (@radial_shrink_inner R n r P hP y hy) sub0r
    (real_seminorm_negate hN.1).
  exact: ltW hy.
- rewrite (radial_shrink_outer_displacement hy).
  exact: lexx.
Qed.
End RadialShrinkMapDisplacement.
