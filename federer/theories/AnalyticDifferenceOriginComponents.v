(** Federer (1969), 3.4.9, p. 337:
    the actual connected components of the difference of
    two analytic varieties form a locally finite family.
    First prove the assertion at the original centre,
    reusing every corrected law of 3.4.8(11). *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets cardinality reals topology.
From Federer Require Import RealNormUP NormMetric GrassmannAbbreviations FiniteCoordinates FiniteDualDimension
  EuclideanInnerProduct InnerNorm HilbertFormCompactness SetGermUP SetGermSealed SetGermLaws SetGermLocality
  FiniteAnalyticVarietyUP FiniteAnalyticVarietyRestriction AnalyticVarietyGermUP
  GermVanishingSealed AnalyticDepthSealed AnalyticGermLocalRepresentative
  AnalyticFiniteStratificationUP AnalyticFiniteStratificationExistence FiniteStrataLocalComponentFiniteness.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section DifferenceComponents.
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

(** Source for [analytic_difference_origin_local_components]: the
    first assertion of 3.4.9, p. 337, at zero.
    Original local representatives provide a common equation
    neighbourhood. The proved strata stay in the original
    difference, so their finite components bound its actual
    components meeting a smaller neighbourhood. *)
Theorem analytic_difference_origin_local_components (S D:set X):
  @is_analytic_variety_germ R X NX hNX 0 (germ S) ->
  @is_analytic_variety_germ R X NX hNX 0 (germ D) ->
  exists O:set X,@open T O /\O 0 /\
    finite_set (@connected_component T (S `\` D) @` ((S `\` D) `&` O)).
Proof.
move=>hS hD.
have [U [hU0 [_ hUS]]]:=@analytic_germ_local_representative R X NX hNX setT S Logic.I openT hS.
have [W [hW0 [hWU hWD]]]:=@analytic_germ_local_representative R X NX hNX U D hU0 hUS.1 hD.
have hWS:=@finite_analytic_variety_open_restriction R X NX hNX U W (U `&` S) hUS hWD.1 hWU.
have hSame:W `&` (U `&` S)=W `&` S.
  apply/seteqP;split.
  - by move=>x [hx [_ hSx]];split.
  - move=>x [hx hSx];split;first exact:hx.
    split;[exact:hWU x hx|exact:hSx].
rewrite hSame in hWS.
pose d:=depth (ideal (germ (W `&` S))).
have [mu [V [F [G [hLaws hInside]]]]]:=@analytic_finite_stratification_exists_at_bound R d n
  W (W `&` S) W (W `&` D) hW0 hWS hW0 hWD (leqnn d).
have hStratumInside i:F i `<=` S `\` D.
  move=>x hx;have [hxW hxS]:=hInside i x hx.
  split;first exact:hxS.
  move=>hxD;apply:(@analytic_stratification_disjoint R n
    (germ (W `&` S)) (germ (W `&` D)) d W (W `&` D) mu V F G hLaws i x hx).
  left;by split.
have hGerm:=analytic_stratification_germ hLaws.
rewrite (@set_germ_neighbourhood_intersection T 0 W S hWD.1 hW0)
  (@set_germ_neighbourhood_intersection T 0 W D hWD.1 hW0)
  (@set_germ_complement_equation T 0 _ _ _ (@SetGerms.laws T 0))
  (@set_germ_intersection_equation T 0 _ _ _ (@SetGerms.laws T 0)) in hGerm.
exact:(@finite_strata_local_component_finiteness T 'I_mu 0 (S `\` D) F hStratumInside
  (analytic_stratification_components hLaws) (esym hGerm)).
Qed.
End DifferenceComponents.
