(** Federer (1969), 2.6.3(1), p. 117: the diagonal over [0,1] for Lebesgue
    and counting measure. Its product measure is infinite and its two
    iterated characteristic integrals are zero and one. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import RealMetricBackground ExtendedRealOrderTopology PartialFunctionBasic
  MeasureUP MeasureBasic MeasureAlmostBasic MeasureIntegralUP MeasureIntegralUniqueness MeasureIntegralGraphEquivalence
  BorelRegularMeasureUP TopologicalBorel CountablyMeasurableUP CountingMeasure CountingMeasureBorel
  LebesgueScalarMeasure StieltjesBorelRegularity IntervalBumpFunctions CountableOrderIntervals MeasureFiniteClosure ProductMeasure ProductBorelRegularity
  ProductAssociativityObstruction RealDiagonalMeasurability ProductSections ProductSetFubini
  CountingProductDiagonal CountingDiagonalSections CountingDiagonalIteratedIntegrals
  PositiveCharacteristicMeasurability MeasureExtendedCharacteristicIntegral
  MeasurableFunctionUP MeasureStepCharacteristic MeasurableRealEmbedding CharacteristicNonzeroLocus
  CharacteristicFunctionUP CharacteristicFunctionSealed ParameterizedIntegral.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Import numFieldTopology.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section Diagonal.
Variable R : realType.
Local Notation mu := (@lebesgue_scalar_measure R).
Local Notation hm := (lebesgue_scalar_is_measure R).
Local Notation beta := (@counting_measure R (Choice.clone R _)).
Local Notation hb := (counting_measure_is_measure R (Choice.clone R _)).
Local Notation nu := (product_measure hm hb).
Local Notation A := ([set x : R | 0 <= x /\ x <= 1]).
Local Notation S := (restricted_diagonal A).

(** Source for [lebesgue_counting_product_borel_regular]: the
    Borel regularity assertion in Federer 2.6.3(1), p. 117.
    Countable bases of the two real lines suffice, although
    the counting factor is not countably measurable. *)
Lemma lebesgue_counting_product_borel_regular : is_borel_regular_measure nu.
Proof.
have [U hU] := @real_line_countable_open_base_exists R.
exact (@product_measure_borel_regular R (Topological.clone R _) (Topological.clone R _)
  mu beta hm hb U U hU hU (lebesgue_scalar_borel_regular R)
  (@counting_metric_borel_regular R (real_line_metric R))).
Qed.

(** Source for [lebesgue_unit_segment_value]: supporting
    value one of the base segment in Federer 2.6.3(1),
    p. 117, using the interval formula of 2.5.17, p. 111. *)
Lemma lebesgue_unit_segment_value : mu A = 1%:E.
Proof.
have he : A = `[0,1].
  apply/seteqP; split=> x; rewrite /= in_itv /=.
  - by move=> [h0 h1]; rewrite h0 h1.
  - by move=> /andP.
by rewrite he lebesgue_scalar_segment ?ler01 // subr0.
Qed.

(** Source for [lebesgue_unit_segment_measurable]: supporting
    measurability of the base segment of the diagonal in
    Federer 2.6.3(1), p. 117. *)
Lemma lebesgue_unit_segment_measurable : measure_measurable mu A.
Proof.
have he : A = `[0,1].
  apply/seteqP; split=> x; rewrite /= in_itv /=.
  - by move=> [h0 h1]; rewrite h0 h1.
  - by move=> /andP.
rewrite he; apply: (borel_regular_borel_measurable hm (lebesgue_scalar_borel_regular R)).
apply: closed_borel_set; exact: segment_closed_real.
Qed.

(** Source for [lebesgue_counting_diagonal_infinite]: the
    product integral's infinite value in Federer 2.6.3(1),
    p. 117, first as the actual diagonal measure. *)
Lemma lebesgue_counting_diagonal_infinite : nu S = +oo%E.
Proof.
apply: atomless_counting_diagonal_infinite; first exact: lebesgue_scalar_singleton.
by rewrite lebesgue_unit_segment_value lte_fin ltr01.
Qed.

(** Source for [lebesgue_counting_diagonal_iterates]: both
    displayed iterated integrals in Federer 2.6.3(1),
    p. 117, with their exact values zero and one. *)
Lemma lebesgue_counting_diagonal_iterates (s : R * R -> R) :
  is_characteristic_function S s ->
  is_measure_integral beta
    (parameterized_integral mu (fun y => partial_function_total (fun x => (s (x,y))%:E))) 0%E /\
  is_measure_integral mu
    (parameterized_integral beta (fun x => partial_function_total (fun y => (s (x,y))%:E))) 1%:E.
Proof.
move=> hs; have h := @atomless_counting_diagonal_iterated_integrals R (Choice.clone R _) mu hm A s
  (@lebesgue_scalar_singleton R) lebesgue_unit_segment_measurable hs.
by rewrite lebesgue_unit_segment_value in h.
Qed.

(** Source for [lebesgue_counting_diagonal_not_countably_measurable]:
    failure of the set hypothesis of Fubini in Federer
    2.6.3(1), p. 117. If the diagonal were countably
    product measurable, its horizontal integral would equal
    infinity by 2.6.2(3), contradicting its value zero. *)
Lemma lebesgue_counting_diagonal_not_countably_measurable :
  ~ measure_countably_measurable nu S.
Proof.
move=> hS; have hi := (@product_set_fubini R (Choice.clone R _) (Choice.clone R _) mu beta hm hb S hS).2.2.2.
have he : (fun y => mu (product_horizontal_section S y)) = (fun _ : R => 0%E).
  apply: funext=> y; exact (@atomless_diagonal_horizontal_zero R (Choice.clone R _) mu hm A (@lebesgue_scalar_singleton R) y).
rewrite he lebesgue_counting_diagonal_infinite in hi.
have hz := @nonnegative_extended_constant_integral R (Choice.clone R _) beta hb 0%E (lexx _).
rewrite mul0e in hz.
have hh := measure_integral_unique hi hz; discriminate hh.
Qed.

(** Source for [lebesgue_counting_diagonal_measurable]: the
    measurability assertion in Federer 2.6.3(1), p. 117.
    Rational cuts give a direct measurable decomposition of
    the diagonal from the two strict-order triangles. *)
Lemma lebesgue_counting_diagonal_measurable : measure_measurable nu S.
Proof.
have hO t : measure_measurable mu [set x | x < t].
  apply: (borel_regular_open_measurable (lebesgue_scalar_borel_regular R)).
  exact: order_strict_lower_ray_open.
have hC t : measure_measurable mu [set x | x <= t].
  have hu : measure_measurable mu [set x | t < x].
    apply: (borel_regular_open_measurable (lebesgue_scalar_borel_regular R)).
    exact: order_strict_upper_ray_open.
  have he : [set x : R | x <= t] = ~` [set x : R | t < x].
    apply/seteqP; split=> x /=.
    - move=> h; apply/negP; by rewrite -leNgt.
    - move=> /negP h; by rewrite leNgt.
  rewrite he; exact: measure_measurable_complement hu.
exact (@real_closed_segment_diagonal_measurable R mu beta hm hb 0 1 hO hC
  (fun t => @counting_measure_measurable R (Choice.clone R _) [set x | x < t])
  (fun t => @counting_measure_measurable R (Choice.clone R _) [set x | x <= t])
  lebesgue_unit_segment_measurable (@counting_measure_measurable R (Choice.clone R _) A)).
Qed.

(** Source for [lebesgue_counting_diagonal_characteristic_example]:
    complete characteristic-function assertions in Federer
    2.6.3(1), p. 117. The product integral exists
    with value infinity; both iterated integrals exist with
    distinct finite values; countable measurability of the set
    and function both fail. Borel regularity is supplied by
    [lebesgue_counting_product_borel_regular]. *)
Theorem lebesgue_counting_diagonal_characteristic_example (s : R * R -> R) :
  is_characteristic_function S s ->
  is_measure_measurable_function nu
    (partial_function_total (fun p => (s p)%:E : extended_real_line R)) /\
  is_measure_integral nu (partial_function_total (fun p => (s p)%:E)) +oo%E /\
  is_measure_integral beta
    (parameterized_integral mu (fun y => partial_function_total (fun x => (s (x,y))%:E))) 0%E /\
  is_measure_integral mu
    (parameterized_integral beta (fun x => partial_function_total (fun y => (s (x,y))%:E))) 1%:E /\
  ~ measure_countably_measurable nu S /\
  ~ is_countably_measure_measurable_function nu (0 : extended_real_line R)
    (partial_function_total (fun p => (s p)%:E : extended_real_line R)).
Proof.
move=> hs; have hnu := product_measure_is_measure hm hb.
have hmeas := lebesgue_counting_diagonal_measurable.
have [hi hj] := lebesgue_counting_diagonal_iterates hs.
split.
- apply: (measurable_total_real_embedding hnu).
  exact (@measurable_total_characteristic_function R (Choice.clone (R*R)%type _) nu hnu S s hs hmeas).
split.
- have h := @measure_total_characteristic_integral R (Choice.clone (R*R)%type _) nu hnu S s hs hmeas.
  by rewrite lebesgue_counting_diagonal_infinite in h.
split=> //; split=> //; split; first exact: lebesgue_counting_diagonal_not_countably_measurable.
move=> hc; have h := countably_measurable_function_locus hc.
rewrite (extended_characteristic_nonzero_locus hs) in h.
exact: lebesgue_counting_diagonal_not_countably_measurable h.
Qed.
End Diagonal.
