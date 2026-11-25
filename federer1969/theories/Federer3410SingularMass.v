(** Federer (1969), 3.4.10, p. 337:
    every compact subset of the analytic domain
    meets the nonregular part in finite H^(m-1)
    mass. Use the original opaque global dimension
    and regular part; no measurability is assumed. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric GrassmannAbbreviations
  EuclideanInnerProduct InnerNorm InnerMetric HilbertFormCompactness InnerNormTopologyAdapters
  SetGermUP AnalyticVarietyGermUP AnalyticSetNonemptyCentres AnalyticSetLocalDepth
  AnalyticSetDimension BoundedNaturalSupremumUP AnalyticRegularLocusUP
  AnalyticRegularLocusSealed AnalyticCentreSingularMass CompactLocalFiniteMass
  HausdorffMeasure MeasureUP MeasureBasic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [federer_3_4_10_compact_singular_mass]: the
    second compact-measure assertion of 3.4.10,
    p. 337, for positive global dimension.
    The regular set is the opaque set
    with the original neighbourhood laws. *)
Theorem federer_3_4_10_compact_singular_mass (R:realType) n
    (U S C:set (R_n R n)) u:
  let hB:=@euclidean_inner_productP R n in
  let hNX:=inner_norm_real_norm hB in
  let T:=Topological.clone (real_norm_metric_space hNX) _ in
  @open T U ->S `<=` U ->
  @is_analytic_set_in R (R_n R n) (inner_norm hB) hNX U S ->
  @analytic_set_dimension R n S=u.+1 ->
  @compact (inner_metric_space hB) C ->C `<=` U ->
  (@hausdorff_measure R (inner_metric_space hB) u
    (C `&` (S `\` @AnalyticRegularLocus.value R n u.+1 U S))< +oo)%E.
Proof.
move=>hB hNX T hU hSU hAnalytic hDimension hCompact hCU.
pose E:=inner_metric_space hB.
pose L:=@AnalyticRegularLocus.value R n u.+1 U S.
rewrite setIC.
apply:(@compact_local_finite_mass R [the topologicalType of E]
  (@hausdorff_measure R E u) (S `\` L) C
  (@hausdorff_measure_is_measure R E u) hCompact)=>a ha.
case:(pselect (S a))=>haS.
- have hBound:(@analytic_set_local_depth R n S a<=u.+1)%N.
    rewrite -hDimension.
    exact:(@bounded_natural_supremum_upper (R_n R n) S
      (@analytic_set_local_depth R n S) (@analytic_set_dimension R n S)
      (@analytic_set_dimension_laws R n S) a haS).
  have [W [hW [hWa hMass]]]:=@analytic_centre_singular_positive_mass R n
    U S L a u hU (hCU a ha) (hAnalytic a (hCU a ha)) hBound
    (@AnalyticRegularLocus.laws R n u.+1 U S).
  exists W;split;first exact:(inner_norm_openP hB W).2 hW.
  by split.
- have [W [hW [hWa hEmpty]]]:=@analytic_set_outside_empty_neighbourhood R
    (R_n R n) (inner_norm hB) hNX U S a hAnalytic (hCU a ha) haS.
  exists W;split;first exact:(inner_norm_openP hB W).2 hW.
  split;first exact:hWa.
  have hSingularEmpty:(S `\` L) `&` W=set0.
    apply/seteqP;split;last by move=>x.
    move=>x [[hxS _] hxW];have h:(S `&` W) x by split.
    by rewrite hEmpty in h.
  by rewrite hSingularEmpty (measure_empty (@hausdorff_measure_is_measure R E u)) lt0y.
Qed.
