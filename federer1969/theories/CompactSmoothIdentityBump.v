(** Federer (1969), 4.1.15, p. 373, final example:
    a concrete compactly supported smooth map equal to the
    identity near zero. Reuse the original unit bump from
    3.1.13 and the compact local Lipschitz bound from
    4.1.14. This is an existence witness, not a new
    definition of smoothness. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals topology lra.
From Federer Require Import Hom TensorUP RealNormUP NormMetric NormDifferentialUP
  NormDifferentialLinear NormDifferentialLocalAgreement NormOpenDomainLaws
  NormClassOneUP NormRegularity NormRegularityOperations NormRegularityBilinear
  NormClassHigherUP ContinuousMultilinearUP ContinuousMultilinearSealed
  GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct InnerNorm
  HilbertFormCompactness InnerSmoothUnitBump NormUnitBumpUP NormUnitBumpSealed
  FiniteNormMetricCompactness CurrentJoinSliceMapClass
  NormLocalLipschitzScalarProduct EuclideanLocalLipschitzCompactSupport.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section CompactSmoothIdentityBump.
Variable R:realType.
Local Notation X:=(R_n R 1%N).
Local Notation B:=(@euclidean_inner_product R 1%N).
Local Notation hB:=(@euclidean_inner_productP R 1%N).
Local Notation NX:=(inner_norm hB).
Local Notation hNX:=(inner_norm_real_norm hB).
Local Notation NS:=(fun t:R^o=>`|t|).
Local Notation hNS:=(@scalar_absolute_value_norm R).
Local Notation Full:=(fun _:X=>True).
Local Notation mu:=(inner_smooth_unit_bump hB).
Local Notation hMu:=(inner_smooth_unit_bump_laws hB).
Local Notation Id:=(hom_of_linear (@linear_id R X)).

(** Source for [compact_smooth_identity_bump]: a smooth compact
    local identity is a witness for the last paragraph of
    4.1.15, p. 373. Its value uses only the opaque
    unit bump laws of 3.1.13, p. 224. *)
Definition compact_smooth_identity_bump (x:X):X:=mu x*:x.
Local Notation F:=compact_smooth_identity_bump.

(** Source for [compact_smooth_identity_bump_smooth]: the original
    cutoff product is smooth by the product law of
    3.1.11, p. 220, supporting 4.1.15, p. 373. *)
Theorem compact_smooth_identity_bump_smooth:
  norm_class_all_orders hNX hNX Full F.
Proof.
have hMuSmooth:norm_class_all_orders hNX hNS Full mu.
  move=>k.
  exact:(@NormUnitBump.smooth R X NX B hNX
    (inner_product_squared_norm_specification hB)
    (fun j=>@ContinuousMultilinear.space R j X R^o NX NS hNX hNS)
    (fun j=>@ContinuousMultilinear.evaluation R j X R^o NX NS hNX hNS)
    (fun j=>@ContinuousMultilinear.norm R j X R^o NX NS hNX hNS)
    (fun j=>@ContinuousMultilinear.laws R j X R^o NX NS hNX hNS) k).
move=>k;exact:(norm_class_scalar_product (hMuSmooth k)
  (@current_join_slice_identity_smooth R 1%N k)).
Qed.

(** Source for [compact_smooth_identity_bump_plateau]: the map
    equals x on the closed unit ball, supporting the
    derivative-at-zero requirement of 4.1.15, p. 373. *)
Theorem compact_smooth_identity_bump_plateau x:NX x<= 1->F x=x.
Proof.
move=>hx;by rewrite /compact_smooth_identity_bump
  (norm_unit_bump_inner hMu hx) scale1r.
Qed.

(** Source for [compact_smooth_identity_bump_zero]: the map
    takes zero to zero, as used in the original
    point-support example of 4.1.15, p. 373. *)
Theorem compact_smooth_identity_bump_zero:F 0=0.
Proof.
by rewrite /compact_smooth_identity_bump scaler0.
Qed.

(** Source for [compact_smooth_identity_bump_off]: the map
    vanishes outside the closed radius-two ball, using the
    literal unit bump of 3.1.13, p. 224, for the
    test-function sequence in 4.1.15, p. 373. *)
Theorem compact_smooth_identity_bump_off x:2<=NX x->F x=0.
Proof.
move=>hx;by rewrite /compact_smooth_identity_bump
  (norm_unit_bump_outer hMu hx) scale0r.
Qed.

(** Source for [compact_smooth_identity_bump_bound]: the chosen
    compact test witness for 4.1.15, p. 373, has
    norm at most two everywhere. *)
Theorem compact_smooth_identity_bump_bound x:NX (F x)<=2.
Proof.
case:(leP (NX x) 2)=>hx.
- rewrite /compact_smooth_identity_bump inner_normZ
    (ger0_norm (andP (norm_unit_bump_range hMu x)).1).
  have hProduct:=ler_wpM2r (inner_norm_nonnegative hB x)
    (andP (norm_unit_bump_range hMu x)).2.
  rewrite mul1r in hProduct;exact:le_trans hProduct hx.
- rewrite (compact_smooth_identity_bump_off (ltW hx)) inner_norm0.
  exact:ler0n.
Qed.

(** Source for [compact_smooth_identity_bump_differential_zero]: the
    actual derivative at zero is the identity, by locality
    on the bump plateau. This supplies the slopes in
    the last example of 4.1.15, p. 373. *)
Theorem compact_smooth_identity_bump_differential_zero:
  has_norm_differential NX NX Full F (0:X) Id.
Proof.
have hBound:norm_bounded_linear NX NX Id.
  exists 1;split;first exact:ler01.
  by move=>x;rewrite /Id hom_of_linearE /= mul1r.
have hId:=@norm_differential_linear R X X NX NX hNX hNX
  Full (0:X) Id (norm_full_domain_interior NX (0:X)) hBound.
apply:(@norm_differential_local_agreement R X X NX NX hNX Full Full
  (fun x:X=>x) F (0:X) Id 1 ltr01 _ _ hId).
- by move=>h _;split.
- move=>h hh _;rewrite add0r.
  exact:esym (compact_smooth_identity_bump_plateau (ltW hh)).
Qed.

(** Source for [compact_smooth_identity_bump_lipschitz]: compact
    support and smoothness give one finite whole-space bound
    for the rescaling example in 4.1.15, p. 373.
    Reuse the already proved compact localisation theorem. *)
Theorem compact_smooth_identity_bump_lipschitz:
  exists L:R,0<L /\forall x y,NX (F x-F y)<=L*NX (x-y).
Proof.
pose C:set (real_norm_metric_space hNX):=[set x|NX x<=2].
have hCompact:compact C:=@finite_norm_metric_ball_compact R X NX hNX
  1%N (@coordinate_basis R 1%N) (@coordinate_basisP R 1%N) 2.
have hOff:forall x,~C x->F x=0.
  move=>x hx;apply:compact_smooth_identity_bump_off;apply:ltW.
  by rewrite ltNge;exact/negP.
have hLocal:=@norm_class_one_locally_metric_lipschitz R X X NX NX hNX hNX
  Full F ((@norm_class_firstP R X X NX NX hNX hNX Full F).1
    (compact_smooth_identity_bump_smooth 1%N)).
exact:(@euclidean_local_lipschitz_compact_support_global R 1%N X NX hNX F C
  hCompact hOff hLocal).
Qed.
End CompactSmoothIdentityBump.
Arguments compact_smooth_identity_bump (R) x : clear implicits.
