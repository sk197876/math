(** A concrete project counterexample to the spherical parenthesis
    in Federer 2.10.11, p. 176. All original hypotheses are proved.
    The image has spherical mass at least two while the compact
    source has mass at most one, under an isometry of least constant one. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  cardinality reals constructive_ereal topology.
From Federer Require Import BinarySequenceCylinders BinaryPrefixDistanceUP BinaryPrefixMetric
  BinaryPrefixCompact BinaryPrefixSphericalUpper BinaryVerticalEmbedding
  BinaryVerticalSphericalLower MetricProductBackground RealMetricBackground
  CompleteMetricUP TopologicalBorel LipschitzUP LipschitzConstant
  PartialFunctionBasic ExtendedRealOrderTopology MappingMultiplicity PartitionMultiplicityIntegral
  MeasureUP MeasureIntegralUP MeasureIntegralBounds MeasureIntegralUniqueness
  BorelRegularMeasureUP HausdorffMeasure RealPower.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [binary_vertical_embedding_lipschitzian]: the project
    counterexample satisfies the exact Lipschitzian hypothesis of
    Federer 2.10.11, p. 176, with a positive bound one. *)
Lemma binary_vertical_embedding_lipschitzian (R:realType):
  is_metric_lipschitz setT (@binary_vertical_embedding R).
Proof.
exists 1%R;split;first exact:ltr01.
exact:binary_vertical_embedding_lipschitz.
Qed.

(** Source for [binary_vertical_embedding_least_constant]: the
    actual least constant is one in the project counterexample to
    Federer 2.10.11, p. 176. Two constant binary sequences give
    an attained distance one, without an assumed optimality law. *)
Lemma binary_vertical_embedding_least_constant (R:realType)
    (hlip:is_metric_lipschitz setT (@binary_vertical_embedding R)):
  metric_lipschitz_constant hlip= 1%R.
Proof.
have hUpper:=metric_lipschitz_constant_minimal hlip
  (@binary_vertical_embedding_lipschitz R).
pose x:binary_prefix_metric R:=fun _=>false.
pose y:binary_prefix_metric R:=fun _=>true.
have hfirst:binary_first_difference x y 0.
  split;first by [].
  by move=> k;rewrite ltn0.
have hd:(mdist x y= 1)%R.
  rewrite binary_prefix_metric_distance
    (binary_prefix_distance_first (BinaryPrefixDistance.laws R) hfirst).
  by rewrite expn0 /= invr1.
have hLower:=@metric_lipschitz_constant_attained R
  (binary_prefix_metric R)
  (metric_product (binary_prefix_metric R) (real_line_metric R))
  setT (@binary_vertical_embedding R) hlip x y I I.
rewrite binary_vertical_embedding_isometry hd mulr1 in hLower.
apply/eqP;by rewrite eq_le hUpper hLower.
Qed.

(** Source for [federer_2_10_11_spherical_counterexample]: project
    correction of the parenthetical spherical claim in Federer
    2.10.11, p. 176. The source is compact, complete and separable,
    the source subset is Borel, the map is isometric with least
    constant one, and the actual multiplicity integral exists and
    strictly exceeds the printed spherical right hand side. *)
Theorem federer_2_10_11_spherical_counterexample (R:realType)
    (hlip:is_metric_lipschitz setT (@binary_vertical_embedding R)):
  let X:=binary_prefix_metric R in
  let Y:=metric_product X (real_line_metric R) in
  let f:=@binary_vertical_embedding R in
  let beta:=@spherical_measure R Y 1 in
  let F:=partial_function_total
    (fun y=>(@mapping_multiplicity R X Y f setT y:extended_real_line R)) in
  compact (@setT X) /\ is_complete_metric_space X /\
    (exists D:set X,countable D /\ dense D) /\ borel_set (@setT X) /\
    metric_lipschitz_constant hlip= 1%R /\
    is_measure_integral beta F (measure_lower_integral beta F) /\
    (real_power (metric_lipschitz_constant hlip) 1)%:E*
      @spherical_measure R X 1 setT<measure_lower_integral beta F.
Proof.
move=> X Y f beta F.
have hLip:=@binary_vertical_embedding_least_constant R hlip.
have hm:is_measure beta:=@spherical_measure_is_measure R Y 1.
have hreg:is_borel_regular_measure beta:=@spherical_measure_borel_regular R Y 1.
have hB:=@binary_vertical_image_borel R.
have hMeas:=@borel_regular_borel_measurable R Y beta hm hreg _ hB.
have hInj:{in setT &,injective f}.
  move=> x y _ _;exact:binary_vertical_embedding_injective.
have hi:=@injective_multiplicity_integral R X Y f setT beta hm hInj hMeas.
have he:measure_lower_integral beta F=beta (f @` setT).
  exact:(measure_lower_integral_unique (measure_lower_integral_specification beta F) hi.2.2).
split;first exact:(@binary_prefix_metric_compact R).
split;first exact:(@binary_prefix_metric_complete R).
split;first exact:(@binary_prefix_metric_separable R).
split;first by apply:open_borel_set;exact:openT.
split;first exact hLip.
split;first by rewrite he.
rewrite hLip real_power_one_base mul1e he.
apply:le_lt_trans (@binary_prefix_spherical_length_upper R) _.
apply:lt_le_trans (_:1<2%:E) (@binary_vertical_spherical_mass_lower R).
by rewrite lte_fin ltr1n.
Qed.
