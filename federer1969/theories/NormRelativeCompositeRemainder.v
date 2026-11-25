(** Federer (1969), 3.2.17, p. 255:
    the final two-remainder estimate proves
    differentiability relative to the parametrized set.
    This supporting norm-space form uses only
    an actual linear extension of the composite
    differential and the inverse distance bound. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals lra ring.
From Federer Require Import Hom Bilinear RealNormUP NormDifferentialUP RelativeDifferentialUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [norm_relative_composite_first_order]:
    the displayed difference-quotient argument of
    Federer 3.2.17, p. 255. The
    inverse Lipschitz inequality converts the source
    error to a target first-order remainder.
    The affine value is exactly F(psi(a)). *)
Theorem norm_relative_composite_first_order (R : realType)
    (X Y Z : lmodType R) (NX : X -> R) (NY : Y -> R) (NZ : Z -> R)
    (hNX : is_real_norm NX) (hNY : is_real_norm NY) (hNZ : is_real_norm NZ)
    (K : set X) (psi : X -> Y) (F : Y -> Z) a
    (L : Hom X Y) (H : Hom X Z) (Q : Hom Y Z) (lambda : R) :
  has_norm_differential NX NY setT psi a L ->
  has_norm_differential NX NZ setT (fun x=>F (psi x)) a H ->
  norm_bounded_linear NY NZ Q ->
  (forall v, Q (L v)=H v) -> 0<lambda -> K a ->
  (forall x, K x -> NX (x-a)<=lambda*NY (psi x-psi a)) ->
  has_relative_first_order_approximation NY NZ setT (psi @` K) F (psi a) (F (psi a)) Q.
Proof.
move=> hPsi hComp hQ hQL hLam ha hInv.
split; first exact hQ.
split; first by move=> _.
split.
- exists 1; split; first exact: ltr01; by move=> x _ _.
- move=> e he.
  have [C [hC hBound]] := hQ.
  have hC1 : 0<C+1 by lra.
  pose t := e/(2*lambda*(C+1)).
  have hDen : 0<2*lambda*(C+1) by rewrite !mulr_gt0 ?ltr0n.
  have ht : 0<t by rewrite /t divr_gt0.
  have htEq : t*(2*lambda*(C+1))=e by rewrite /t divfK ?gt_eqF.
  have [d [hd hPsiR]] := norm_differential_remainder hPsi ht.
  have [s [hs hCompR]] := norm_differential_remainder hComp ht.
  pose delta := Num.min d s/lambda.
  have hDelta : 0<delta by rewrite /delta divr_gt0 // lt_min hd hs.
  exists delta; split=> // y [x hx <-] _ hsmall.
  have hX := hInv x hx.
  have hY0 := real_seminorm_nonnegative hNY.1 (psi x-psi a).
  have hX0 := real_seminorm_nonnegative hNX.1 (x-a).
  have hYdelta : lambda*NY (psi x-psi a)<Num.min d s.
    by move: hsmall; rewrite /delta ltr_pdivlMr // mulrC.
  have hxMin := le_lt_trans hX hYdelta.
  have hMinD : Num.min d s<=d by rewrite ge_min lexx.
  have hMinS : Num.min d s<=s by rewrite ge_min lexx orbT.
  have hxd : NX (x-a)<d := lt_le_trans hxMin hMinD.
  have hxs : NX (x-a)<s := lt_le_trans hxMin hMinS.
  have hshift : a+(x-a)=x by rewrite addrC subrK.
  have hp := hPsiR (x-a) I hxd; rewrite hshift in hp.
  have hc := hCompR (x-a) I hxs; rewrite hshift in hc.
  have hdecomp : F (psi x)-F (psi a)-Q (psi x-psi a)=
    (F (psi x)-F (psi a)-H (x-a)) + Q (L (x-a)-(psi x-psi a)).
    by rewrite (linB (hom_linear Q) (L (x-a)) (psi x-psi a)) hQL addrA subrK.
  have hNorm : NZ (Q (L (x-a)-(psi x-psi a)))<=C*(t*NX (x-a)).
    apply: (le_trans (hBound _) _).
    rewrite (real_seminorm_subtract hNY.1).
    exact: (ler_wpM2l hC hp).
  have hSum := le_trans (real_seminorm_triangle hNZ.1
    (F (psi x)-F (psi a)-H (x-a)) (Q (L (x-a)-(psi x-psi a)))) (lerD hc hNorm).
  rewrite -hdecomp in hSum.
  have hError : t*NX (x-a)+C*(t*NX (x-a))<=e*NY (psi x-psi a).
    have hScale := ler_wpM2l (mulr_ge0 (ltW ht) (ltW hC1)) hX.
    nra.
  exact: le_trans hSum hError.
Qed.
