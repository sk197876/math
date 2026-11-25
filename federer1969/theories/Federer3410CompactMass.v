(** Federer (1969), 3.4.10, p. 337:
    every compact subset of the original analytic
    domain meets S in finite H^m mass,
    where m is its actual global dimension. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals
  constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric GrassmannAbbreviations EuclideanInnerProduct
  InnerNorm InnerMetric HilbertFormCompactness InnerNormTopologyAdapters
  SetGermUP AnalyticVarietyGermUP AnalyticSetLocalCover
  FiniteAnalyticVarietyUP FiniteAnalyticVarietyRelativeClosed
  AnalyticSetLocalDepth AnalyticSetDimension BoundedNaturalSupremumUP
  AnalyticCentreFiniteMass CompactLocalFiniteMass HausdorffMeasure MeasureUP MeasureBasic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [federer_3_4_10_compact_mass]: the first
    measure assertion of 3.4.10, p. 337,
    at the exact original global dimension, for
    every compact C contained in U. Local
    irreducible representatives and the existing compact-cover
    theorem supply the bound; no mass or
    measurability conclusion is a premise. *)
Theorem federer_3_4_10_compact_mass (R:realType) n (U S C:set (R_n R n)) m:
  let hB:=@euclidean_inner_productP R n in
  let hNX:=inner_norm_real_norm hB in
  let T:=Topological.clone (real_norm_metric_space hNX) _ in
  @open T U ->S `<=` U ->
  @is_analytic_set_in R (R_n R n) (inner_norm hB) hNX U S ->
  @analytic_set_dimension R n S=m ->
  @compact (inner_metric_space hB) C ->C `<=` U ->
  (@hausdorff_measure R (inner_metric_space hB) m (C `&` S)< +oo)%E.
Proof.
move=>hB hNX T hU hSU hAnalytic hDimension hCompact hCU.
pose X:=R_n R n;pose E:=inner_metric_space hB.
rewrite setIC.
apply:(@compact_local_finite_mass R [the topologicalType of E]
  (@hausdorff_measure R E m) S C (@hausdorff_measure_is_measure R E m) hCompact)=>a ha.
case:(pselect (S a))=>haS.
- have hBound:(@analytic_set_local_depth R n S a<=m)%N.
    rewrite -hDimension;exact:(@bounded_natural_supremum_upper (R_n R n) S (@analytic_set_local_depth R n S)
      (@analytic_set_dimension R n S) (@analytic_set_dimension_laws R n S) a haS).
  have [W [hW [hWa hMass]]]:=@analytic_centre_local_finite_mass R n S a m
    (hAnalytic a (hCU a ha)) hBound.
  exists W;split;first exact:(inner_norm_openP hB W).2 hW.
  by split.
- have hCover:=(@analytic_set_local_cover_equivalence R X (inner_norm hB) hNX U S).1 hAnalytic.
  have [V [haV hVariety]]:=hCover a (hCU a ha).
  have [K [hK hEquation]]:=finite_analytic_variety_relative_closed_form hVariety.
  have haNotK:~K a.
    move=>haK;apply:haS;have h:(V `&` S) a by rewrite hEquation;split.
    exact:h.2.
  pose W:=V `&` ~` K.
  have hW:@open T W:=openI hVariety.1 (closed_openC hK).
  exists W;split;first exact:(inner_norm_openP hB W).2 hW.
  split;first by split.
  have hEmpty:S `&` W=set0.
    apply/seteqP;split;last by move=>x.
    move=>x [hxS [hxV hxNot]];apply:hxNot.
    have h:(V `&` S) x by split.
    by rewrite hEquation in h;exact:h.2.
  by rewrite hEmpty (measure_empty (@hausdorff_measure_is_measure R E m)) lt0y.
Qed.
