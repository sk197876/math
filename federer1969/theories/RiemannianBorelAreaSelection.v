(** Federer (1969), 3.2.46, p. 282: the
    original-domain Borel univalent selection used in the
    Riemannian extension of 3.2.5, pp. 244–245.
    Proved local coordinate selections and a countable
    refinement discharge all geometric selection hypotheses. *)
From mathcomp Require Import all_boot all_order all_algebra reals
  classical_sets constructive_ereal topology.
From Federer Require Import EuclideanInnerProduct InnerMetric RiemannianTensorUP RiemannianMetricCarrier
  RiemannianHausdorff RiemannianPathLipschitz RiemannianChartReference
  RiemannianVolumeCompletion RiemannianLocalAreaSelection LocalBorelUnivalentSelection
  NormMetricScaleContinuity LipschitzUP BorelFunctionBasic TopologicalBorel
  MeasureUP MeasureFiniteClosure ExtendedRealOrderTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [riemannian_borel_area_selection]: the
    actual Riemannian analogue of 3.2.4, p. 244,
    supporting the full signed area alternatives in
    3.2.46, p. 282. The original path-Lipschitz map
    has a Borel univalent subset of every original
    completed-measurable S on which its actual Jacobian
    is positive; the original image deficit is null.
    All dimensions and infinite masses remain. *)
Theorem riemannian_borel_area_selection (R : realType) m n A B g h
    (hg : @is_continuous_riemannian_tensor R m A g)
    (hh : @is_continuous_riemannian_tensor R n B h)
    (f : riemannian_metric_space hg -> riemannian_metric_space hh)
    (hp : 0<=m%:R :> R) (S : set (riemannian_metric_space hg)) :
  is_riemannian_path_lipschitz f ->
  measure_measurable (riemannian_hausdorff_measure hg m%:R hp) S ->
  exists W : set (riemannian_metric_space hg),
    borel_set W /\ W `<=` S `&` positive_riemannian_area_locus f /\
    (forall x y, W x -> W y -> f x=f y -> x=y) /\
    borel_set (f @` W) /\
    riemannian_hausdorff_measure hh m%:R hp ((f @` S) `\` (f @` W))=0%E.
Proof.
move=> hLip hS.
pose X := [the metricType R of riemannian_metric_space hg].
pose Y := [the metricType R of riemannian_metric_space hh].
pose E := [the metricType R of inner_metric_space (@euclidean_inner_productP R m)].
pose phi := @riemannian_chart_reference R m A g hg.
pose beta := riemannian_hausdorff_measure hh m%:R hp.
have hPhi := @riemannian_chart_reference_is_measure R m A g hg.
have hReference := (@riemannian_volume_reference_measurable_iff R m A g hg hp S).1 hS.
have hCont : continuous f.
  have [K [hK hBound]] := @riemannian_path_lipschitz_carrier R m n A B g h hg hh f hLip.
  apply: (@metric_fixed_lipschitz_continuous R X Y f K (ltW hK)).
  by move=> x y; exact: hBound.2 x y Logic.I Logic.I.
have [C hBase] := @riemannian_chart_countable_open_base R m A g hg.
apply: (@local_borel_univalent_selection R X Y f beta S (positive_riemannian_area_locus f) C
  (@riemannian_hausdorff_is_measure R n B h hh m%:R hp) (continuous_borel_function hCont) hBase).
move=> a.
have [U [K [F [hU [hUa [hUA [hK [hBound [hRange hAgreement]]]]]]]]] :=
  @riemannian_path_map_local_coordinates R m n A B g h hg hh f hLip a.
pose V : set X := (fun x : X=>(val x : E)) @^-1` U.
have hV : open V.
  exact (@open_comp X E (fun x=>val x) U
    (fun x _=>@riemannian_chart_inclusion_continuous R m A g hg x) hU).
have hVMeas := @riemannian_chart_reference_borel_measurable R m A g hg V (open_borel_set hV).
have hT := @measure_measurable_intersection R X phi hPhi S V hReference hVMeas.
have hFLip : is_metric_lipschitz setT F by exists K; split.
have [W [hW [hWSub [hWInj [hWImage hDeficit]]]]] :=
  @riemannian_local_borel_area_selection R m n A B g h hg hh f U F hRange hp (S `&` V)
    hU hUA hFLip hAgreement hT (fun x hx=>hx.2).
exists V; split; first exact hV; split; first exact hUa.
exists W; split; first exact hW; split.
- move=> x hx; have [hTx hPx] := hWSub x hx; split; [exact hTx.1 | exact hPx].
split; first exact hWInj; split; [exact hWImage | exact hDeficit].
Qed.
