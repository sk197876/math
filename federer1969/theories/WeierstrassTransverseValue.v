(** Federer (1969), 3.4.7, p. 325: specialization
    of actual transverse coefficients at the origin agrees
    with their original values. Only sealed representative
    and pullback equations are used. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import Hom RealNormUP AnalyticGermRepresentatives AnalyticGermUP
  AnalyticGermRingLaws AnalyticGermRing AnalyticGermValueUP AnalyticGermValueSealed
  AnalyticPullbackRepresentative AnalyticPullbackSealed WeierstrassTransverseUP WeierstrassTransversePullback.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [weierstrass_transverse_pullback_value]: a
    transverse coefficient and its actual ambient pullback
    have the same original centre value, supporting
    the specialization in 3.4.7, p. 325. *)
Theorem weierstrass_transverse_pullback_value (R:realType) (X K:lmodType R)
    (NX:X->R) (NK:K->R) (hNX:is_real_norm NX) (hNK:is_real_norm NK)
    (v:X) (xi:Hom X R^o) (inclusion:Hom K X) (projection:Hom X K)
    (hSplit:is_weierstrass_transverse_space NX NK v xi inclusion projection)
    (alpha:@analytic_germ_ring R K NK hNK (projection 0)):
  @AnalyticGermValue.map R X NX hNX 0
    (@weierstrass_transverse_ring_pullback R X K NX NK hNX hNK v xi inclusion projection hSplit alpha) =
  @AnalyticGermValue.map R K NK hNK (projection 0) alpha.
Proof.
have [f hf]:=@analytic_germ_has_representative R K NK hNK (projection 0) alpha.
rewrite -hf.
pose hProjection:=@weierstrass_transverse_projection_analytic R X K NX NK hNX hNK
  v xi inclusion projection hSplit.
change (@AnalyticGermValue.map R X NX hNX 0
    (@AnalyticPullback.map R X K NX NK hNX hNK setT projection 0 hProjection (analytic_germ f)) =
  @AnalyticGermValue.map R K NK hNK (projection 0) (analytic_germ f)).
rewrite (@AnalyticPullback.laws R X K NX NK hNX hNK setT projection 0 hProjection)
  (@AnalyticGermValue.laws R X NX hNX 0)
  (@AnalyticGermValue.laws R K NK hNK (projection 0)).
reflexivity.
Qed.
