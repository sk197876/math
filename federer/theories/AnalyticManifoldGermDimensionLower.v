(** Federer (1969), 3.4.10, p. 338:
    a genuine analytic k-manifold patch forces
    the containing analytic germ to have dimension
    at least k. Reuse the null representative
    and manifold nonnullity proved in 3.4.8(13), p. 335. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormMetric GrassmannAbbreviations
  FiniteCoordinates FiniteDualDimension EuclideanInnerProduct InnerNorm HilbertFormCompactness
  SetGermUP SetGermOrder AnalyticVarietyGermUP GermVanishingSealed AnalyticDepthSealed
  AnalyticSubmanifoldUP AnalyticGermHigherDegreeNull SubmanifoldGermNonNull.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [analytic_manifold_germ_dimension_lower]: the
    lower dimension bound needed for the cited
    example in 3.4.10, p. 338.
    Existing higher-degree nullity and actual positive
    manifold mass give the bound directly;
    no new dimension or measure argument is assumed. *)
Theorem analytic_manifold_germ_dimension_lower (R:realType) n k
    (Z:set (R_n R n))
    (alpha:@set_germ_space (Topological.clone (real_norm_metric_space
      (inner_norm_real_norm (@euclidean_inner_productP R n))) _) 0):
  let X:=R_n R n in
  let hB:=@euclidean_inner_productP R n in
  let NX:=inner_norm hB in
  let hNX:=inner_norm_real_norm hB in
  let T:=Topological.clone (real_norm_metric_space hNX) _ in
  @is_analytic_variety_germ R X NX hNX 0 alpha ->
  @is_euclidean_analytic_submanifold R n k Z ->
  @set_germ T 0 Z<>@set_germ T 0 set0 ->
  set_germ_subset (@set_germ T 0 Z) alpha ->
  (k<=@AnalyticDepth.value R X (@euclidean_inner_product R n) hB n
    (@coordinate_basis R n) (@coordinate_basisP R n) (dual_basis (@coordinate_basisP R n))
    (@AnalyticSetIdeal.value R X NX hNX 0 alpha))%N.
Proof.
move=>X hB NX hNX T hAnalytic hManifold hNonempty hContained.
case hBound:(k<=@AnalyticDepth.value R X (@euclidean_inner_product R n) hB n
    (@coordinate_basis R n) (@coordinate_basisP R n) (dual_basis (@coordinate_basisP R n))
    (@AnalyticSetIdeal.value R X NX hNX 0%R alpha))%N;first done.
have hSmall:(@AnalyticDepth.value R X (@euclidean_inner_product R n) hB n
    (@coordinate_basis R n) (@coordinate_basisP R n) (dual_basis (@coordinate_basisP R n))
    (@AnalyticSetIdeal.value R X NX hNX 0%R alpha)<k)%N by rewrite ltnNge hBound.
have [K [hK hNull]]:=@analytic_germ_higher_degree_null_representative R n alpha k hAnalytic hSmall.
have hSubset:set_germ_subset (@set_germ T 0 Z) (@set_germ T 0 K) by rewrite hK.
exfalso.
exact:(@analytic_submanifold_germ_nonnull R n k Z K hManifold hNonempty hSubset hNull).
Qed.
