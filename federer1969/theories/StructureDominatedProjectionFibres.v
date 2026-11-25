(** Federer (1969), 3.3.16, p. 299: both original
    projection conditions from the independent replacement comparisons. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets cardinality
  reals constructive_ereal topology.
From Federer Require Import EuclideanInnerProduct InnerMetric EuclideanProjectionSpace EuclideanLebesgueDimensions
  EuclideanMetricSeparability StructureReplacementMeasureUP StructureProjectionConditions
  ProjectionMultiplicityIntegral BorelMultiplicityIntegral BorelImageCoverCost
  BorelCaratheodoryMeasure BorelCaratheodoryMeasureBound MappingMultiplicity CountingMeasure PartialFunctionUP PartialFunctionBasic
  ExtendedRealOrderTopology MeasureUP MeasureBasic MeasureIntegralBounds MeasureIntegralUP MeasureIntegralUniqueness
  MeasureUpperIntegralPositivePart MeasureAlmostUP MeasureAlmostBasic TopologicalBorel BorelRegularMeasureUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [structure_dominated_projection_conditions]:
    the 2.10.8/2.10.10 modification required in Federer 3.3.16,
    p. 299. The independent positive finite comparison constant
    gives null-subset preservation for EVERY original subset and
    a bound on the actual original counting integral at EVERY
    projection. Finite original source mass then makes original
    fibres finite almost everywhere. No finite Hausdorff mass is
    supplied or inferred, in particular for actual Gross measure. *)
Theorem structure_dominated_projection_conditions (R:realType) n m
    (phi:set (inner_metric_space (@euclidean_inner_productP R n))->\bar R)
    (E:set (inner_metric_space (@euclidean_inner_productP R n)))
    (p:euclidean_projection_space R n m):
  is_structure_replacement_measure m phi ->borel_set E ->phi E< +oo ->
  structure_projection_preserves_null_subsets phi E p /\structure_projection_almost_finite_fibres E p.
Proof.
move=>hLaws hE hFinite.
have hPhi:=structure_replacement_measure_law hLaws.
have hRegular:=structure_replacement_borel_regular hLaws.
have [c [hc hBound]]:=structure_replacement_projection_bound hLaws.
split.
- move=>B hBE hZero.
  have h:=hBound B p; rewrite hZero mule0 in h.
  apply/eqP; rewrite eq_le (measure_nonnegative (euclidean_lebesgue_is_measure R m)) andbT.
  exact:h.
- pose X:=inner_metric_space (@euclidean_inner_productP R n).
  pose Y:=inner_metric_space (@euclidean_inner_productP R m).
  pose f:X->Y:=euclidean_projection_linear p.
  pose L:=@euclidean_lebesgue_measure R m.
  have hL:=euclidean_lebesgue_is_measure R m.
  have [D [hD hDense]]:=euclidean_metric_separable R n.
  have hImage S:borel_set S ->measure_measurable L (f @` S).
    exact:(@euclidean_projection_borel_image_measurable R n m p S).
  have hIntegral:=@borel_multiplicity_integral R [the metricType R of X] [the choiceType of Y]
    f L hL D E hD hDense hImage hE.
  have hCost S:borel_set S ->borel_image_cover_cost f L S<=c%:E*phi S.
    move=>_; exact:hBound S p.
  have hMeasureBound:=@borel_caratheodory_measure_bound R [the metricType R of X]
    (borel_image_cover_cost f L) (@borel_image_cover_cost_laws R [the metricType R of X]
      [the choiceType of Y] f L hL) phi hPhi hRegular D c hD hDense (ltW hc) hCost E.
  have hENum:phi E \is a fin_num by rewrite (ge0_fin_numE (measure_nonnegative hPhi E)).
  have hValue:phi E=(fine (phi E))%:E by rewrite fineK.
  have hCountFinite:borel_caratheodory_measure (borel_image_cover_cost f L) E< +oo.
    apply:le_lt_trans hMeasureBound _; rewrite hValue -EFinM; exact:ltry.
  pose F:=partial_function_total (fun y:Y=>(@mapping_multiplicity R [the choiceType of X] Y f E y:extended_real_line R)).
  have hUpper:measure_upper_integral L F< +oo.
    have hEqual:=measure_upper_integral_unique (measure_upper_integral_specification L F) hIntegral.2.1.
    by rewrite hEqual.
  have hAlmost:=(@measure_finite_upper_integral_consequences R [the choiceType of Y] L hL F hUpper).2.
  apply:(measure_almost_everywhere_mono hL _ hAlmost)=>y [v [hv hBelow]].
  have hValueCount:@mapping_multiplicity R [the choiceType of X] Y f E y=v:=hv.
  apply:contrapT=>hInfinite.
  have hCount:=@counting_measure_infinite R [the choiceType of X] (mapping_fibre f E y) hInfinite.
  rewrite /mapping_multiplicity hCount in hValueCount.
  by rewrite -hValueCount ltxx in hBelow.
Qed.
