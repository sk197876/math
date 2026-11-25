(** Federer (1969), 3.4.8(11),(13), pp. 333, 336:
    full dimension gives the whole analytic germ.
    This endpoint adapter reuses the proved positive-ambient
    theorem and the zero-depth point theorem; in R^0
    the whole space is the original point. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormMetric GrassmannAbbreviations FiniteCoordinates FiniteDualDimension
  EuclideanInnerProduct EuclideanStiefelInnerSplitting InnerNorm HilbertFormCompactness
  SetGermUP AnalyticGermRing GermVanishingSealed AnalyticVarietyGermUP AnalyticDepthSealed
  AnalyticZeroDepthPointGerm AnalyticFullDimensionalCut.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [analytic_full_dimension_whole_germ]: the original
    full-dimensional endpoint in 3.4.8(13), p. 336,
    including the zero ambient dimension. *)
Theorem analytic_full_dimension_whole_germ (R:realType) n
    (alpha:@set_germ_space (Topological.clone (real_norm_metric_space
      (inner_norm_real_norm (@euclidean_inner_productP R n))) _) 0):
  @is_analytic_variety_germ R (R_n R n) (inner_norm (@euclidean_inner_productP R n))
    (inner_norm_real_norm (@euclidean_inner_productP R n)) 0 alpha ->
  alpha<>@set_germ (Topological.clone (real_norm_metric_space
    (inner_norm_real_norm (@euclidean_inner_productP R n))) _) 0 set0 ->
  @AnalyticDepth.value R (R_n R n) (@euclidean_inner_product R n) (@euclidean_inner_productP R n)
    n (@coordinate_basis R n) (@coordinate_basisP R n) (dual_basis (@coordinate_basisP R n))
    (@AnalyticSetIdeal.value R (R_n R n) (inner_norm (@euclidean_inner_productP R n))
      (inner_norm_real_norm (@euclidean_inner_productP R n)) 0 alpha)=n ->
  alpha=@set_germ (Topological.clone (real_norm_metric_space
    (inner_norm_real_norm (@euclidean_inner_productP R n))) _) 0 setT.
Proof.
case:n alpha=>[|n] alpha hAlpha hNonempty hDepth.
- have hDual i j:dual_basis (@coordinate_basisP R 0) i (@coordinate_basis R 0 j)=if i==j then 1 else 0.
    by rewrite dual_basisE eq_sym.
  have hPoint:=@analytic_zero_depth_point_germ R (R_n R 0) (@euclidean_inner_product R 0)
    (@euclidean_inner_productP R 0) 0 (@coordinate_basis R 0) (@coordinate_basisP R 0)
    (dual_basis (@coordinate_basisP R 0)) hDual alpha hAlpha hNonempty hDepth.
  have hWhole:[set (0:R_n R 0)]=setT.
    apply/seteqP;split;first by move=>x hx.
    move=>x _;apply/ffunP=>i;by case:i=>i.
  by rewrite hWhole in hPoint.
- have hDual i j:dual_basis (@coordinate_basisP R n.+1) i (@coordinate_basis R n.+1 j)=if i==j then 1 else 0.
    by rewrite dual_basisE eq_sym.
  exact:(@analytic_full_dimensional_variety_whole R (R_n R n.+1) (@euclidean_inner_product R n.+1)
    (@euclidean_inner_productP R n.+1) n (@coordinate_basis R n.+1) (@coordinate_basisP R n.+1)
    (@euclidean_coordinate_orthonormal_family R n.+1) (dual_basis (@coordinate_basisP R n.+1))
    hDual alpha hAlpha hNonempty hDepth).
Qed.
