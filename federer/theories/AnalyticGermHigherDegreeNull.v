(** Federer (1969), 3.4.8(13), p. 335:
    the original analytic variety germ has a representative
    null at every integer degree above its actual depth.
    This is the upper half of the dimension comparison,
    proved by the complete stratification (11). *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals
  constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric GrassmannAbbreviations FiniteCoordinates
  FiniteDualDimension EuclideanInnerProduct InnerNorm InnerMetric HilbertFormCompactness
  SetGermUP SetGermSealed SetGermLaws AnalyticVarietyGermUP FiniteAnalyticVarietyUP
  FiniteAnalyticVarietyBoundary GermVanishingSealed AnalyticDepthSealed
  AnalyticFiniteStratificationUP AnalyticFiniteStratificationExistence AnalyticStrataHigherDegreeNull
  HausdorffMeasure.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section UpperNullity.
Variable R:realType.
Variable n:nat.
Local Notation X:=(R_n R n).
Local Notation NX:=(inner_norm (@euclidean_inner_productP R n)).
Local Notation hNX:=(inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation E:=(Topological.clone (real_norm_metric_space hNX) _).
Local Notation germ:=(@set_germ E 0).
Local Notation ideal:=(@AnalyticSetIdeal.value R X NX hNX 0).
Local Notation depth:=(@AnalyticDepth.value R X (@euclidean_inner_product R n)
  (@euclidean_inner_productP R n) n (@coordinate_basis R n) (@coordinate_basisP R n)
  (dual_basis (@coordinate_basisP R n))).

(** Source for [analytic_germ_higher_degree_null_representative]:
    the H^(m+1)-null representative in the proof of
    3.4.8(13), p. 335, in the stronger
    form for every q>m. Its hypotheses contain
    no image-measure or dimension-comparison conclusion. *)
Theorem analytic_germ_higher_degree_null_representative (alpha:@set_germ_space E 0) q:
  @is_analytic_variety_germ R X NX hNX 0 alpha ->
  (depth (ideal alpha)<q)%N ->
  exists S:set X,germ S=alpha /\
    @hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R n)) q S=0%E.
Proof.
move=>[U [H [hU0 [hH hAlpha]]]] hDQ.
pose d:=depth (ideal alpha).
have hBound:(depth (ideal (germ H))<=d)%N by rewrite hAlpha;exact:leqnn.
have hEmpty:=@finite_analytic_variety_domain_empty R X NX hNX U hH.1.
have [mu [V [S [G [hLaws hInside]]]]]:=@analytic_finite_stratification_exists_at_bound R d n
  U H U set0 hU0 hH hU0 hEmpty hBound.
have hGerm:=analytic_stratification_germ hLaws.
rewrite (@set_germ_complement_equation E 0 _ _ _ (@SetGerms.laws E 0)) setC0
  (@set_germ_intersection_equation E 0 _ _ _ (@SetGerms.laws E 0)) setIT hAlpha in hGerm.
exists (\bigcup_i S i);split;first exact:esym hGerm.
exact:(@analytic_strata_higher_degree_null R n d q mu V S hDQ
  (analytic_stratification_functional hLaws)).
Qed.
End UpperNullity.
