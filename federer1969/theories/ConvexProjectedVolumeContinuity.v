(** Federer (1969), 3.2.35, p. 272:
    Borel measurability of actual composite projected
    volumes in Steiner's repeated projection average.
    Existing compact upper and convex lower
    continuity prove the needed fixed-source continuity. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology lra.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerNorm InnerMetric InnerConvex
  InnerConvexNeighbourhoods CoveringFamilyUP MetricBoundedUnion MetricBoundedClosureLaws
  EuclideanProjectionSpace EuclideanProjectionMetric ProjectedVolumeMeasurability ProjectedVolumeBounds
  CompactConvexProjectedVolumeLower CompactProjectedVolumeUpperContinuity ConvexProjectedClosureVolume
  RealMetricBackground ExtendedRealOrderTopology MeasurableRealEmbedding PartialFunctionBasic PartialFunctionPreimages
  MeasureUP MeasureAlmostBasic BorelRegularMeasureUP BorelFunctionBasic MeasurableFunctionUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [compact_convex_projected_volume_scalar_continuous]:
    supporting the actual repeated projection
    integral in Federer 3.2.35, p. 272.
    The independently proved compact upper and
    convex lower neighbourhoods give fixed-source
    continuity, without invoking Steiner's formula
    or the later varying-body theorem 3.2.36.
    The explicit norm bound is discharged below. *)
Lemma compact_convex_projected_volume_scalar_continuous (R:realType) n m
    (S:set (inner_metric_space (@euclidean_inner_productP R n))) (c:R):
  (forall x,S x ->(inner_norm (@euclidean_inner_productP R n) x<=c)%R) ->
  compact S ->is_inner_convex S ->
  continuous (fun p:euclidean_projection_space R n m=>
    (fine (projected_volume_function S p):real_line_metric R)).
Proof.
move=>hb hK hc.
pose P := euclidean_projection_space R n m.
pose f (p : P) : real_line_metric R := fine (projected_volume_function S p).
have hfin p := @projected_volume_function_finite R n m S c hb p.
move=> p A hA.
have [e he hball] := proj1 (metricType_numDomainType.nbhs_mdistP (f p) A) hA.
have hlo : (f p-e)%R%:E<projected_volume_function S p.
  rewrite -(fineK (hfin p)) lte_fin; change (is_true (f p-e<f p)%R).
  have he0 : (0<e)%R := he; lra.
have hhi : projected_volume_function S p<(f p+e)%R%:E.
  rewrite -(fineK (hfin p)) lte_fin; change (is_true (f p<f p+e)%R).
  have he0 : (0<e)%R := he; lra.
have [V [hV [hpV hVl]]] := @compact_convex_projected_volume_lower_neighbourhood R n m S p (f p-e)%R hK hc hlo.
have [W [hW [hpW hWh]]] := @compact_projected_volume_upper_neighbourhood R n m S p (f p+e)%R hK hhi.
have hnV : nbhs p V by rewrite openE in hV; exact: hV p hpV.
have hWTop:@open (euclidean_projection_space R n m) W:=(orthogonal_projection_metric_openE W).1 hW.
have hnW : nbhs p W by rewrite openE in hWTop; exact: hWTop p hpW.
apply: (@filterS _ (nbhs p) _ (V `&` W) _ _ (@filterI _ (nbhs p) _ V W hnV hnW))=> q [hqV hqW].
have hl : (f p-e<f q)%R.
  have h := hVl q hqV; by rewrite -(fineK (hfin q)) lte_fin in h.
have hu : (f q<f p+e)%R.
  have h := hWh q hqW; by rewrite -(fineK (hfin q)) lte_fin in h.
apply: hball; change (is_true (mdist (f p) (f q)<e)%R).
rewrite real_line_metric_distanceE ltr_norml; apply/andP; split; lra.
Qed.

(** Source for [convex_projected_volume_continuous]:
    supporting legitimate composition of actual
    projection volumes in Federer 3.2.35,
    p. 272. Proved closure agreement and
    compact convex closure give continuity for
    every original nonempty bounded convex set,
    including lower-dimensional or nonmeasurable ones. *)
Theorem convex_projected_volume_continuous (R:realType) n m
    (S:set (inner_metric_space (@euclidean_inner_productP R n))):
  S!=set0 ->is_inner_convex S ->metric_set_bounded S ->
  continuous (projected_volume_function (m:=m) S:euclidean_projection_space R n m->extended_real_line R).
Proof.
move=>hNonempty hS hBound.
pose X:=inner_metric_space (@euclidean_inner_productP R n).
have hClosureBound:=metric_bounded_closure hBound.
have [c [_ hRadius]]:=@metric_bounded_distance_bound R [the metricType R of X]
  (closure S) (0%R:X) hClosureBound.
have hNormBound x:closure S x ->(inner_norm (@euclidean_inner_productP R n) x<=c)%R.
  move=>hx; have hh:=hRadius x hx.
  by rewrite inner_metric_distanceE sub0r inner_normN in hh.
have hCompact:=euclidean_bounded_closure_compact hBound.
have hConvex:=@inner_convex_closure R (R_n R n) (@euclidean_inner_product R n)
  (@euclidean_inner_productP R n) S hS.
have hCont:=@compact_convex_projected_volume_scalar_continuous R n m (closure S) c hNormBound hCompact hConvex.
have hFunction:(fun p:euclidean_projection_space R n m=>(fine (projected_volume_function (closure S) p))%:E)=
    projected_volume_function (m:=m) S.
  apply:funext=>p; rewrite -(@convex_projected_closure_volume R n m p S hNonempty hS hBound).
  exact:fineK (@projected_volume_function_finite R n m (closure S) c hNormBound p).
rewrite -hFunction; move=>p.
exact:continuous_comp (hCont p) (@real_extended_embedding_continuous R (fine (projected_volume_function (closure S) p))).
Qed.

(** Source for [convex_projected_volume_parameter_measurable]:
    supporting measurability of composite projection
    volumes in Federer 3.2.35, p. 272.
    The actual fixed-source volume is continuous,
    so a continuous parameter map has Borel
    inverse images before completion. This avoids
    an unjustified composition of merely completed
    measurable functions. *)
Theorem convex_projected_volume_parameter_measurable (R:realType) n m (Z:topologicalType)
    (mu:set Z->\bar R) (u:Z->euclidean_projection_space R n m)
    (S:set (inner_metric_space (@euclidean_inner_productP R n))):
  is_measure mu ->is_borel_regular_measure mu ->continuous u ->
  S!=set0 ->is_inner_convex S ->metric_set_bounded S ->
  is_measure_measurable_function mu (partial_function_total (fun z=>projected_volume_function S (u z))).
Proof.
move=>hm hRegular hU hNonempty hS hBound.
have hVolume:=@convex_projected_volume_continuous R n m S hNonempty hS hBound.
have hComposite:continuous (fun z:Z=>(projected_volume_function S (u z):extended_real_line R)).
  move=>z; exact:continuous_comp (hU z) (hVolume (u z)).
constructor.
- rewrite partial_function_total_domain; exact:measure_almost_everywhere_true hm.
- move=>V hV; rewrite partial_function_total_preimage.
  apply:(borel_regular_borel_measurable hm hRegular).
  exact (@continuous_borel_function Z [the topologicalType of extended_real_line R]
    (fun z=>projected_volume_function S (u z)) hComposite V hV).
Qed.
