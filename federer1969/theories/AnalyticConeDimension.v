(** Federer (1969), 3.4.11, p. 338:
    the global dimension of the homogeneous polynomial
    majorant is bounded by its original germ dimension
    at zero. The existing stratification supplies a null
    germ representative; positive dilation and the proved
    global null-dimension connection finish the assertion. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals
  constructive_ereal topology.
From Federer Require Import Hom RealNormUP NormMetric GrassmannAbbreviations FiniteCoordinates
  FiniteDualDimension EuclideanInnerProduct InnerNorm InnerMetric HilbertFormCompactness
  SetGermUP GermVanishingSealed AnalyticDepthSealed AnalyticVarietyGermUP
  AnalyticSetDimension AnalyticGermHigherDegreeNull AnalyticConeGlobalNull AnalyticNullSetDimension.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [analytic_cone_global_dimension_bound]: the
    literal global dimension bound of the homogeneous
    polynomial majorant in 3.4.11, p. 338.
    The source cone may be reducible, and every
    finite ambient dimension, including zero, remains. *)
Theorem analytic_cone_global_dimension_bound (R:realType) n (S:set (R_n R n)):
  let X:=R_n R n in
  let B:=@euclidean_inner_product R n in
  let hB:=@euclidean_inner_productP R n in
  let NX:=inner_norm hB in
  let hNX:=inner_norm_real_norm hB in
  let T:=Topological.clone (real_norm_metric_space hNX) _ in
  let d:=@AnalyticDepth.value R X B hB n (@coordinate_basis R n) (@coordinate_basisP R n)
    (dual_basis (@coordinate_basisP R n)) (@AnalyticSetIdeal.value R X NX hNX 0 (@set_germ T 0 S)) in
  @is_analytic_set_in R X NX hNX setT S ->
  (forall t:R,0<t ->forall x,S x ->S (t*:x)) ->
  (@analytic_set_dimension R n S<=d)%N.
Proof.
move=>X B hB NX hNX T d hAnalytic hCone.
have [A [hGerm hNull]]:=@analytic_germ_higher_degree_null_representative R n
  (@set_germ T 0 S) d.+1 (hAnalytic 0 Logic.I) (ltnSn d).
apply:(@analytic_null_set_dimension_bound R n S d hAnalytic).
exact:(@analytic_cone_global_null_from_germ R n S A d.+1 hCone hGerm hNull).
Qed.
