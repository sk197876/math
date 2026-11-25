(** Federer (1969), 4.1.15, p. 372: exact norm and zero
    locus of the original radial shrink map. These are
    consequences of its two independently stated value laws. *)
From mathcomp Require Import all_boot all_order all_algebra
  reals ring lra.
From Federer Require Import RealNormUP InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct RadialShrinkMapUP
  RadialShrinkMapDisplacement.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Section RadialShrinkMapNorm.
Variable R : realType.
Variable n : nat.
Local Notation X := (R_n R n).
Local Notation N := (inner_norm (@euclidean_inner_productP R n)).
Variable r : R.
Hypothesis hr : 0 < r.
Variable P : X -> X.
Hypothesis hP : is_radial_shrink_map r P.

(** Source for [radial_shrink_outer_norm]: the defining
    radial formula in 4.1.15, p. 372, has length |y|-r
    on |y|>=r. This supplies the mixed cases in the
    original assertion Lip(Psi_r)<= 1. *)
Theorem radial_shrink_outer_norm y :
  r <= N y -> N (P y) = N y-r.
Proof.
move=> hy.
have hPositive : 0 < N y := lt_le_trans hr hy.
have hCancel : (r/N y)*N y=r by rewrite divfK ?gt_eqF.
have hFactor : 0 <= 1-r/N y.
  rewrite -(ler_pM2r hPositive) mul0r mulrBl mul1r
    hCancel subr_ge0; exact: hy.
rewrite (radial_shrink_outer hP hy) inner_normZ
  (ger0_norm hFactor) mulrBl mul1r hCancel.
by [].
Qed.

(** Source for [radial_shrink_zero]: Psi_r(0)=0 follows
    from the inner case of the definition, 4.1.15,
    p. 372; no positive ambient dimension is needed. *)
Theorem radial_shrink_zero : P 0=0.
Proof.
apply:(radial_shrink_inner hP).
by rewrite inner_norm0.
Qed.

(** Source for [radial_shrink_zero_iff]: the zero locus
    of the map defined in 4.1.15, p. 372, is the
    closed radius-r ball. The boundary is included. *)
Theorem radial_shrink_zero_iff y :
  P y=0 <-> N y<=r.
Proof.
split.
- move=> hZero; case:(leP (N y) r)=> // hOuter.
  have hNorm:=radial_shrink_outer_norm (ltW hOuter).
  rewrite hZero inner_norm0 in hNorm.
  have hPositive:0<N y-r by rewrite subr_gt0.
  by move:hPositive;rewrite -hNorm ltxx.
- exact:(radial_shrink_closed_inner hr hP).
Qed.

(** Source for [radial_shrink_norm_bound]: the radial
    formula of 4.1.15, p. 372, never increases the
    length of a vector. This includes r=|y| and n=0. *)
Theorem radial_shrink_norm_bound y : N (P y)<=N y.
Proof.
case:(leP (N y) r)=> hy.
- rewrite ((radial_shrink_zero_iff y).2 hy) inner_norm0.
  exact:inner_norm_nonnegative.
- rewrite (radial_shrink_outer_norm (ltW hy)) lerBlDr lerDl.
  exact:ltW hr.
Qed.
End RadialShrinkMapNorm.
