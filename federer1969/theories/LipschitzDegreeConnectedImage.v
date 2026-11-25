(** Federer (1969), 4.1.26, p. 384:
    if A is connected and f(A) misses
    f(Bdry A), the original signed degree
    is Lebesgue almost constant on f(A).
    Connectedness puts the entire image in
    one complementary component; no openness or
    target-image measurability premise is added. *)
From mathcomp Require Import all_boot all_order all_algebra
  classical_sets reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric InnerNorm InnerMetric HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct MetricDiameter LipschitzUP LipschitzBasic
  MetricLocalLipschitzContinuity EuclideanLebesgueDimensions MeasureUP MeasureAlmostUP
  PartialFunctionUP LipschitzDegreeSealed LipschitzDegreeBoundaryImage LipschitzDegreeConstancy
  ComponentwiseAlmostConstancy
  CoveringFamilyUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [lipschitz_degree_connected_image_almost_constant]:
    the first sentence of 4.1.26 on
    p. 384. A may be an
    arbitrary bounded measurable connected set; its
    image may be empty or have measure zero. *)
Theorem lipschitz_degree_connected_image_almost_constant (R:realType)
    (h2:(1+1:R)!=0) m (f:R_n R m->R_n R m)
    (hLip:@is_metric_lipschitz R
      (inner_metric_space (@euclidean_inner_productP R m))
      (inner_metric_space (@euclidean_inner_productP R m)) setT f)
    (A:set (R_n R m))
    (hA:measure_measurable (@euclidean_lebesgue_measure R m) A)
    (hBound:@metric_set_bounded R
      (inner_metric_space (@euclidean_inner_productP R m)) A):
  @connected (real_norm_metric_space
    (inner_norm_real_norm (@euclidean_inner_productP R m))) A->
  (forall y,(f @` A) y->~(f @` lipschitz_degree_source_boundary A) y)->
  exists c:R,measure_almost_everywhere_on (@euclidean_lebesgue_measure R m)
    (f @` A) [set y|partial_function_graph (@LipschitzDegree.value R m f A) y c].
Proof.
move=>hConnected hDisjoint.
pose NT:=real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R m)).
have hLocal:@is_locally_metric_lipschitz R NT NT setT f:=metric_lipschitz_is_local hLip.
have hContinuous:continuous (f:NT->NT):=metric_local_lipschitz_continuous_whole hLocal.
have hImageConnected:@connected NT (f @` A):=
  connected_continuous_connected hConnected (continuous_subspaceT hContinuous).
exact:(@componentwise_almost_constant_on_connected_set R NT
  (@euclidean_lebesgue_measure R m) (euclidean_lebesgue_is_measure R m)
  (~`(f @` lipschitz_degree_source_boundary A)) (f @` A)
  (@LipschitzDegree.value R m f A) hImageConnected hDisjoint
  (@lipschitz_degree_component_almost_constant R h2 m f hLip A hA hBound)).
Qed.
