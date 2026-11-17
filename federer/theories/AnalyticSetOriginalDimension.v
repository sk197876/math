(** Federer (1969), 3.4.10, p. 337:
    identify the translated local ideal depth with
    the original opaque nonempty germ dimension
    of 3.4.8(3), p. 326. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormMetric GrassmannAbbreviations FiniteCoordinates
  FiniteDualDimension EuclideanInnerProduct InnerNorm HilbertFormCompactness SetGermUP
  AnalyticVarietyGermUP AnalyticSetLocalDepth AnalyticVarietyGermDimensionSealed
  AnalyticVarietyGermDimensionLaws.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [analytic_set_local_depth_original_dimension]: the
    exact original local dimension in the
    supremum of 3.4.10, p. 337.
    Translate the actual centre to zero and
    apply the proved equality with ideal depth;
    the result is independent of both analytic
    and nonempty-germ proof witnesses. *)
Theorem analytic_set_local_depth_original_dimension (R:realType) n (S:set (R_n R n)) a:
  let hB:=@euclidean_inner_productP R n in
  let NX:=inner_norm hB in
  let hNX:=inner_norm_real_norm hB in
  let T:=Topological.clone (real_norm_metric_space hNX) _ in
  forall hA:@is_analytic_variety_germ R (R_n R n) NX hNX 0 (@set_germ T 0 [set x|S (a+x)]),
  forall hNonempty:@set_germ T 0 [set x|S (a+x)]<>@set_germ T 0 set0,
  @analytic_set_local_depth R n S a=
    @AnalyticVarietyGermDimension.value R (R_n R n) (@euclidean_inner_product R n) hB n
      (@coordinate_basis R n) (@coordinate_basisP R n) (dual_basis (@coordinate_basisP R n))
      (@set_germ T 0 [set x|S (a+x)]) hA hNonempty.
Proof.
move=>hB NX hNX T hA hNonempty.
exact:esym (@analytic_variety_germ_dimension_depth R (R_n R n)
  (@euclidean_inner_product R n) hB n (@coordinate_basis R n)
  (@coordinate_basisP R n) (dual_basis (@coordinate_basisP R n))
  (@set_germ T 0 [set x|S (a+x)]) hA hNonempty).
Qed.
