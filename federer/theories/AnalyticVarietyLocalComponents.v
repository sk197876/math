(** Federer (1969), 3.4.8(11), pp. 333–335,
    discharging the compact-component obligation of 3.4.5,
    p. 321: an original analytic germ has an
    actual neighbourhood meeting only finitely many components
    of any original representative. All strata are
    kept inside that representative before component counting. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets cardinality reals topology.
From Federer Require Import RealNormUP NormMetric GrassmannAbbreviations FiniteCoordinates FiniteDualDimension
  EuclideanInnerProduct InnerNorm HilbertFormCompactness SetGermUP SetGermSealed SetGermLaws SetGermLocality
  FiniteAnalyticVarietyUP FiniteAnalyticVarietyBoundary AnalyticVarietyGermUP GermVanishingSealed AnalyticDepthSealed
  AnalyticGermLocalRepresentative AnalyticFiniteStratificationUP AnalyticFiniteStratificationExistence
  FiniteStrataLocalComponentFiniteness.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section LocalComponents.
Variable R:realType.
Variable n:nat.
Local Notation X:=(R_n R n).
Local Notation NX:=(inner_norm (@euclidean_inner_productP R n)).
Local Notation hNX:=(inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation T:=(Topological.clone (real_norm_metric_space hNX) _).
Local Notation germ:=(@set_germ T 0).
Local Notation depth:=(@AnalyticDepth.value R X (@euclidean_inner_product R n)
  (@euclidean_inner_productP R n) n (@coordinate_basis R n) (@coordinate_basisP R n)
  (dual_basis (@coordinate_basisP R n))).
Local Notation ideal:=(@AnalyticSetIdeal.value R X NX hNX 0).

(** Source for [analytic_variety_germ_origin_local_components]:
    the local component consequence of the complete
    original stratification (11), pp. 333–335.
    The original representative need not be globally
    a finite analytic zero set; only its germ is required. *)
Theorem analytic_variety_germ_origin_local_components (S:set X):
  @is_analytic_variety_germ R X NX hNX 0 (germ S) ->
  exists O:set X,@open T O /\O 0 /\
    finite_set (@connected_component T S @` (S `&` O)).
Proof.
move=>hAnalytic.
have [U [hU0 [_ hVariety]]]:=@analytic_germ_local_representative R X NX hNX setT S Logic.I openT hAnalytic.
have hEmpty:=@finite_analytic_variety_domain_empty R X NX hNX U hVariety.1.
pose d:=depth (ideal (germ (U `&` S))).
have [mu [V [F [G [hLaws hInside]]]]]:=@analytic_finite_stratification_exists_at_bound R d n
  U (U `&` S) U set0 hU0 hVariety hU0 hEmpty (leqnn d).
have hStratumInside i:F i `<=` S by move=>x hx;exact:(hInside i x hx).2.
have hGerm:=analytic_stratification_germ hLaws.
rewrite (@set_germ_complement_equation T 0 _ _ _ (@SetGerms.laws T 0)) setC0
  (@set_germ_intersection_equation T 0 _ _ _ (@SetGerms.laws T 0)) setIT
  (@set_germ_neighbourhood_intersection T 0 U S hVariety.1 hU0) in hGerm.
exact:(@finite_strata_local_component_finiteness T 'I_mu 0 S F hStratumInside
  (analytic_stratification_components hLaws) (esym hGerm)).
Qed.
End LocalComponents.
