(** Federer (1969), 4.1.15, p. 372: local Lipschitz
    regularity and a radius-independent distance bound for
    G_r. This is the bound used before smoothing the
    original f and G_r. *)
From mathcomp Require Import all_boot all_order all_algebra
  reals classical_sets topology lra ring.
From Federer Require Import RealNormUP NormMetric InnerNorm
  HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  LipschitzUP RadialShrinkMapSealed RadialShrinkMapNonexpanding
  RadialAgreementMapUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section RadialAgreementMapLipschitz.
Variable R:realType.
Variables n nu:nat.
Local Notation X:=(R_n R n).
Local Notation Y:=(R_n R nu).
Local Notation NX:=(inner_norm (@euclidean_inner_productP R n)).
Local Notation NY:=(inner_norm (@euclidean_inner_productP R nu)).
Local Notation hNX:=(inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation hNY:=(inner_norm_real_norm (@euclidean_inner_productP R nu)).
Local Notation MX:=(real_norm_metric_space hNX).
Local Notation MY:=(real_norm_metric_space hNY).
Variable r:R.
Hypothesis hr:0<r.
Variables f g G:X->Y.
Hypothesis hG:is_radial_agreement_map r hr f g G.
Local Notation P:=(@RadialShrinkMap.value R nu r hr).
Local Notation hP:=(@RadialShrinkMap.laws R nu r hr).

(** Source for [radial_agreement_lipschitz_bound]: the original
    G_r=f+Psi_r(g-f) in 4.1.15, p. 372, has a
    bound 2 Lip(f)+Lip(g), independent of r. Only the
    actual relative domain is used, and zero bounds remain
    allowed. This supplies the printed uniform derivative bounds. *)
Theorem radial_agreement_lipschitz_bound (A:set X) (Lf Lg:R):
  @is_metric_lipschitz_bound R MX MY A f Lf ->
  @is_metric_lipschitz_bound R MX MY A g Lg ->
  @is_metric_lipschitz_bound R MX MY A G (2*Lf+Lg).
Proof.
move=>hF hGMap;split.
- exact:addr_ge0 (mulr_ge0 (ler0n R 2) hF.1) hGMap.1.
move=>x y hx hy.
change (is_true (NY (G x-G y)<=(2*Lf+Lg)*NX (x-y))).
have hDifference:G x-G y=(f x-f y)+
    (P (g x-f x)-P (g y-f y)).
  rewrite (hG x) (hG y) opprD; by rewrite addrACA.
have hDifferenceInputs:(g x-f x)-(g y-f y)=
    (g x-g y)-(f x-f y).
  by rewrite !opprD !opprK addrACA.
have hPBound:=radial_shrink_nonexpanding hr hP (g x-f x) (g y-f y).
have hInputBound:NY ((g x-f x)-(g y-f y))<=
    NY (g x-g y)+NY (f x-f y).
  rewrite hDifferenceInputs.
  have hTriangle:=real_seminorm_triangle hNY.1 (g x-g y) (-(f x-f y)).
  by rewrite (real_seminorm_negate hNY.1) in hTriangle.
rewrite hDifference.
have hTriangle:=real_seminorm_triangle hNY.1
  (f x-f y) (P (g x-f x)-P (g y-f y)).
have hFx:=hF.2 x y hx hy.
have hGx:=hGMap.2 x y hx hy.
change (is_true (NY (f x-f y)<=Lf*NX (x-y))) in hFx.
change (is_true (NY (g x-g y)<=Lg*NX (x-y))) in hGx.
nra.
Qed.

(** Source for [radial_agreement_locally_lipschitz]: the
    original G_r is locally Lipschitz whenever f and g
    are, as used in the smoothing paragraph of
    Federer 4.1.15, p. 372. No globally Lipschitz
    premise, convex target or target-image assertion is added. *)
Theorem radial_agreement_locally_lipschitz (A:set X):
  @is_locally_metric_lipschitz R MX MY A f ->
  @is_locally_metric_lipschitz R MX MY A g ->
  @is_locally_metric_lipschitz R MX MY A G.
Proof.
move=>hFLocal hGLocal a ha.
have [W [hW [Lf [hLf hF]]]]:=hFLocal a ha.
have [Z [hZ [Lg [hLg hGM]]]]:=hGLocal a ha.
exists (W `&` Z);split;first exact:filterI hW hZ.
exists (2*Lf+Lg);split;first nra.
have hFR:@is_metric_lipschitz_bound R MX MY (A `&` (W `&` Z)) f Lf.
  split;first exact:hF.1.
  move=>x y [hx [hxW hxZ]] [hy [hyW hyZ]].
  exact:hF.2 x y (conj hx hxW) (conj hy hyW).
have hGR:@is_metric_lipschitz_bound R MX MY (A `&` (W `&` Z)) g Lg.
  split;first exact:hGM.1.
  move=>x y [hx [hxW hxZ]] [hy [hyW hyZ]].
  exact:hGM.2 x y (conj hx hxZ) (conj hy hyZ).
exact:radial_agreement_lipschitz_bound hFR hGR.
Qed.
End RadialAgreementMapLipschitz.
