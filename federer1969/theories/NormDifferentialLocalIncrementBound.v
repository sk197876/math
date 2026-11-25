(** Federer (1969), 3.1.1, p. 209: local
    difference quotients bound the actual differential.
    This supporting form is used for the finite
    Riemannian Jacobian bound in the signed coarea
    extension of 3.2.46, p. 282. *)
From mathcomp Require Import all_boot all_order all_algebra reals lra.
From Federer Require Import Hom RealNormUP NormDifferentialUP NormDifferentialDirectional
  NormedCurveDerivativeUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [norm_differential_local_increment_bound]:
    an actual differential inherits a homogeneous increment
    bound on any genuine neighbourhood of its base point,
    supporting 3.2.46, p. 282, from the
    directional quotient formula of 3.1.1, p. 209.
    No global Lipschitz extension or derivative field is
    assumed, and zero direction vectors are retained. *)
Lemma norm_differential_local_increment_bound (R : realType) (X Y : lmodType R)
    (NX : X -> R) (NY : Y -> R) (hNX : is_real_norm NX) (hNY : is_real_norm NY)
    (A : X -> Prop) (f : X -> Y) a (D : Hom X Y) (M : R) :
  has_norm_differential NX NY A f a D ->
  (exists r : R, 0<r /\ forall h, NX h<r -> NY (f (a+h)-f a)<=M*NX h) ->
  forall v, NY (D v)<=M*NX v.
Proof.
move=> hD [r [hr hIncrement]] v; apply/negPn/negP=> hBad.
have hExcess : M*NX v<NY (D v) by rewrite ltNge.
pose e := (NY (D v)-M*NX v)/2.
have he : 0<e by rewrite /e divr_gt0 // subr_gt0.
have [d [hd hNear]] := norm_differential_directional_limit hNX hNY hD v he.
have hV0 := real_seminorm_nonnegative hNX.1 v.
have hV1 : 0<NX v+1 by lra.
pose t := Num.min d (r/(NX v+1))/2.
have ht : 0<t by rewrite /t divr_gt0 // lt_min hd divr_gt0.
have htd : t<d.
  have hMin : Num.min d (r/(NX v+1))<=d by rewrite ge_min lexx.
  have hCancel : t*2=Num.min d (r/(NX v+1)) by rewrite /t divfK ?pnatr_eq0.
  nra.
have htr : t*(NX v+1)<r.
  have hMin : Num.min d (r/(NX v+1))<=r/(NX v+1) by rewrite ge_min lexx orbT.
  have hCancel : t*2=Num.min d (r/(NX v+1)) by rewrite /t divfK ?pnatr_eq0.
  have hScaled := ler_wpM2r (ltW hV1) hMin.
  rewrite divfK ?gt_eqF // in hScaled.
  nra.
have htN : 0<`|t|<d.
  rewrite (ger0_norm (ltW ht)); apply/andP; by split.
have hError := hNear t htN.
pose q := t^-1 *: (f (a+t*:v)-f a).
have hSmall : NX (t*:v)<r.
  rewrite (real_seminorm_scale hNX.1) (ger0_norm (ltW ht)).
  have hVector : NX v<=NX v+1 by rewrite lerDl.
  have hBound := ler_wpM2l (ltW ht) hVector.
  exact:le_lt_trans hBound htr.
have hBound : NY q<=M*NX v.
  rewrite /q (real_seminorm_scale hNY.1) normfV (ger0_norm (ltW ht)).
  have hInc := hIncrement (t*:v) hSmall.
  rewrite (real_seminorm_scale hNX.1) (ger0_norm (ltW ht)) in hInc.
  have hScaled := ler_wpM2l (normr_ge0 t^-1) hInc.
  rewrite normfV (ger0_norm (ltW ht)) in hScaled.
  have hCancel : t^-1*(M*(t*NX v))=M*NX v.
    rewrite (mulrCA t^-1 M (t*NX v)).
    have hInner : t^-1*(t*NX v)=NX v by rewrite mulrA mulVf ?gt_eqF // mul1r.
    by rewrite hInner.
  by rewrite hCancel in hScaled.
have hTriangle := real_seminorm_triangle hNY.1 (D v-q) q.
rewrite subrK (real_seminorm_subtract hNY.1 (D v) q) in hTriangle.
change (is_true (NY (q-D v)<e)) in hError.
rewrite /e in hError; nra.
Qed.
