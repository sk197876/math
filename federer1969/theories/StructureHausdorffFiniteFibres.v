(** Federer (1969), 3.3.13, pp. 297–298: condition (II)
    from actual finite Hausdorff mass and original projection multiplicity. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets cardinality
  reals constructive_ereal topology.
From Federer Require Import EuclideanInnerProduct InnerMetric EuclideanProjectionSpace
  EuclideanLebesgueDimensions EuclideanHausdorffLebesgue EuclideanMetricCompleteness
  EuclideanMetricSeparability HausdorffMeasure LipschitzMultiplicityInteger
  StructureProjectionConditions StructureProjectionContraction MappingMultiplicity CountingMeasure
  PartialFunctionUP PartialFunctionBasic ExtendedRealOrderTopology PartialExtendedOrderLoci
  MeasureUP MeasureIntegralUP MeasureIntegralBounds MeasureIntegralUniqueness
  MeasureUpperIntegralPositivePart MeasureAlmostUP MeasureAlmostBasic TopologicalBorel.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [structure_hausdorff_almost_finite_fibres]: supporting
    original condition (II) in Federer 3.3.13, pp. 297–298. Actual
    2.10.11 bounds the original counting integral by H^m(E). Its upper
    integral is finite, so actual 2.4.3(4) makes the counting function
    finite almost everywhere. Infinite original fibres have infinite
    actual counting measure. Retain every degree, including zero. *)
Lemma structure_hausdorff_almost_finite_fibres (R:realType) n m
    (E:set (inner_metric_space (@euclidean_inner_productP R n)))
    (p:euclidean_projection_space R n m):
  borel_set E ->@hausdorff_measure R
    (inner_metric_space (@euclidean_inner_productP R n)) m E< +oo ->
  structure_projection_almost_finite_fibres E p.
Proof.
move=>hBorel hFinite.
pose X:=inner_metric_space (@euclidean_inner_productP R n).
pose Y:=inner_metric_space (@euclidean_inner_productP R m).
pose f:X->Y:=euclidean_projection_linear p.
pose F:=partial_function_total (fun y:Y=>
  (@mapping_multiplicity R [the choiceType of X] Y f E y:extended_real_line R)).
have [D [hD hDense]]:=euclidean_metric_separable R n.
have [hIntegral hBound]:=@lipschitz_hausdorff_multiplicity_integer_bound R
  [the metricType R of X] [the metricType R of Y] f 1%R m D E
  (@euclidean_metric_complete R n) hD hDense
  (@structure_projection_lipschitz_one R n m p) hBorel.
rewrite expr1n mul1e in hBound.
have hTarget:@hausdorff_measure R [the metricType R of Y] m=@euclidean_lebesgue_measure R m.
  apply:funext=>B; exact:(euclidean_hausdorff_spherical_lebesgue B).1.
rewrite hTarget in hIntegral hBound.
pose L:=@euclidean_lebesgue_measure R m.
have hL:=euclidean_lebesgue_is_measure R m.
have hUpper:measure_upper_integral L F< +oo.
  have hEqual:=measure_upper_integral_unique (measure_upper_integral_specification L F) hIntegral.2.1.
  rewrite hEqual; exact:le_lt_trans hBound hFinite.
have hAlmost:=(@measure_finite_upper_integral_consequences R [the choiceType of Y]
  L hL F hUpper).2.
apply:(measure_almost_everywhere_mono hL _ hAlmost).
move=>y [v [hv hBelow]].
have hValue:@mapping_multiplicity R [the choiceType of X] Y f E y=v:=hv.
apply:contrapT=>hInfinite.
have hCount:=@counting_measure_infinite R [the choiceType of X]
  (mapping_fibre f E y) hInfinite.
have hSame:mapping_fibre f E y=E `&` f @^-1` [set y] by [].
rewrite /mapping_multiplicity hCount in hValue.
by rewrite -hValue ltxx in hBelow.
Qed.
