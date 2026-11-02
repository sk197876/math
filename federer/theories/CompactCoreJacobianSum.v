(** Federer (1969), 3.2.38, p. 275: actual integral
    comparison on a compact core with uniformly small scalar oscillation. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric EuclideanLebesgueDimensions
  EuclideanLebesgueBoxes EuclideanCoordinateCubeUP EuclideanCoordinateCubeGeometry
  JacobianDensityMeasure EuclideanJacobianMeasurable LipschitzUP RealMetricBackground PartialFunctionUP
  ExtendedRealOrderTopology FiniteSubsetActualValueLower FiniteCoreWeightedMeasureBound
  MeasureUP MeasureBasic MeasureSplit MeasureFiniteClosure TopologicalBorel.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [compact_core_jacobian_cube_sum]: the good-cube
    scalar sum in Federer 3.2.38, p. 275, using the earlier
    Lusin theorem 2.3.5 instead of the printed uniform mean
    selection from 2.9.9. Each core value is an actual Jacobian
    graph value. Uniform oscillation bounds the integral inside
    the core; the independently bounded representative controls
    the remaining cube mass. Exact null-face laws justify the
    finite sums for both measures. *)
Lemma compact_core_jacobian_cube_sum (R:realType) m n (G:finType)
    (f:inner_metric_space (@euclidean_inner_productP R m)->
      inner_metric_space (@euclidean_inner_productP R n))
    (J:inner_metric_space (@euclidean_inner_productP R m)->R)
    (E:set (inner_metric_space (@euclidean_inner_productP R m)))
    (corner a:G->R_n R m) (Q:G->set (inner_metric_space (@euclidean_inner_productP R m)))
    (h e M d:R):
  is_metric_lipschitz setT f ->compact E ->
  (forall x,(0<=J x<=M)%R) ->(0<=e)%R ->(0<=M)%R ->
  (forall x,E x ->partial_function_graph (extended_euclidean_jacobian f) x (J x)%:E) ->
  (forall x y,E x ->E y ->@mdist R (inner_metric_space (@euclidean_inner_productP R m)) x y<d ->
    `|J x-J y|<=e) ->
  (forall i,is_euclidean_coordinate_cube (corner i) h (Q i)) ->
  (forall i,(Q i `&` E) (a i)) ->m%:R*h<d ->
  (forall i j,i!=j ->@euclidean_lebesgue_measure R m (Q i `&` Q j)=0%E) ->
  (\sum_i (J (a i))%:E*@euclidean_lebesgue_measure R m (Q i)<=
    euclidean_jacobian_measure f E+e%:E*@euclidean_lebesgue_measure R m E+
      M%:E*@euclidean_lebesgue_measure R m ((\bigcup_i Q i) `\` E))%E.
Proof.
move=>hLip hE hBound he hM hGraph hOsc hQ ha hMesh hNull.
pose X:=inner_metric_space (@euclidean_inner_productP R m).
pose mu:=@euclidean_lebesgue_measure R m.
pose nu:=euclidean_jacobian_measure f.
pose hm:=euclidean_lebesgue_is_measure R m.
pose hn:=euclidean_jacobian_measure_is_measure hLip.
have hEM:measure_measurable mu E.
  apply:euclidean_borel_measurable; exact:closed_borel_set (compact_closed (@metric_hausdorff R X) hE).
have hQM i:measure_measurable mu (Q i).
  apply:euclidean_borel_measurable.
  exact:closed_borel_set (compact_closed (@metric_hausdorff R X) (coordinate_cube_compact (hQ i))).
apply:(@finite_core_weighted_measure_bound R X G mu nu Q E (fun i=>J (a i)) e M
  hm hn hEM (euclidean_jacobian_measure_measurable hLip hEM) hQM
  (fun i=>euclidean_jacobian_measure_measurable hLip (hQM i)) hNull
  (fun i j hij=>euclidean_jacobian_measure_null f (hNull i j hij))
  (fun i=>hBound (a i)) he hM).
move=>i.
pose A:=Q i `&` E.
have hA:measure_measurable mu A:=measure_measurable_intersection hm (hQM i) hEM.
have hFinite:(mu A< +oo)%E.
  apply:le_lt_trans _ (euclidean_compact_finite (coordinate_cube_compact (hQ i))).
  apply:(@measure_mono R X mu hm A (Q i))=>x hx; exact:hx.1.
apply:(@finite_subset_actual_value_lower R X mu A (extended_euclidean_jacobian f)
  J (nu A) (J (a i)) e hm hA hFinite (measure_nonnegative hn A)
  (euclidean_jacobian_measure_integral hLip hA)).
move=>x [hx hEx]; split; first exact:hGraph x hEx.
apply:hOsc (ha i).2 hEx _.
exact:le_lt_trans (coordinate_cube_distance_bound (hQ i) (ha i).1 hx) hMesh.
Qed.
