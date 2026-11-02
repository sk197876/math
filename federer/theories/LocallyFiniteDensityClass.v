(** The assertion psi in M in Federer (1969), 2.9.8, p. 156. Prove the
    measure and Borel-regular laws of a nonnegative measurable density, then
    extend finiteness from bounded measurable targets to arbitrary bounded
    sets by taking closure. its broader class uses a countable finite open
    cover. The result below retains Federer's original bounded-set
    definition. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import ExtendedRealOrderTopology PartialFunctionUP PartialExtendedOrderLoci
  MeasureUP MeasureBasic MeasureAlmostUP MeasurableFunctionUP BorelRegularMeasureUP TopologicalBorel
  CoveringFamilyUP MetricDiameter MetricDiameterClosure MeasureDerivationContext
  MeasureDensityUP MeasureDensityCover MeasureDensityNullSets DensityBorelRegular
  AbsoluteContinuousPart MeasureAbsoluteContinuity.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [locally_finite_density_is_derivation_measure]:
    supporting proof of psi in M in Federer 2.9.8,
    p. 156. Local finiteness is needed only
    on bounded phi-measurable targets: closure preserves
    boundedness and is Borel, so monotonicity gives
    the required bound on every bounded subset. *)
Theorem locally_finite_density_is_derivation_measure (R : realType) (X : metricType R)
    (phi nu : set X -> \bar R) (f : partial_function X (extended_real_line R)) :
  is_derivation_measure phi -> is_measure_density phi f nu -> is_measure_measurable_function phi f ->
  measure_almost_everywhere phi (partial_extended_nonnegative_locus f) ->
  (forall A, metric_set_bounded A -> measure_measurable phi A -> nu A< +oo) ->
  is_derivation_measure nu.
Proof.
move=> hf hn hfm hp hlocal; have hm := derivation_measure_law hf.
have hmn := @measure_density_is_measure R X phi nu hm f hn hp.
constructor; first exact hmn.
- exact (@density_is_borel_regular R X phi nu f hf hn hfm hp).
- move=> A hAb.
  have hclb : metric_set_bounded (closure A) by rewrite /metric_set_bounded extended_metric_diameter_closure.
  have hclm := @borel_regular_borel_measurable R X phi hm (derivation_measure_borel_regular hf)
    (closure A) (@closed_borel_set X (closure A) (@closed_closure X A)).
  exact: le_lt_trans (@measure_mono R X nu hmn A (closure A) (@subset_closure X A)) (hlocal _ hclb hclm).
Qed.

(** Source for [density_equals_continuous_part]: the identity
    psi=psi_phi used in the proof of Federer 2.9.8,
    p. 156. Density measures preserve phi-null
    sets; apply the equality criterion 2.9.2,
    p. 153. No Vitali relation is needed
    for this supporting identity. *)
Lemma density_equals_continuous_part (R : realType) (X : metricType R)
    (phi nu : set X -> \bar R) (f : partial_function X (extended_real_line R)) :
  is_derivation_measure phi -> is_derivation_measure nu -> is_measure_density phi f nu ->
  measure_continuous_part nu phi=nu.
Proof.
move=> hf hn hd; symmetry.
apply: (@continuous_part_equality_iff_absolute_continuity R X phi nu (measure_continuous_part nu phi)
  (derivation_measure_law hf) (derivation_measure_law hn) (derivation_measure_borel_regular hn)
  (measure_continuous_part_specification nu phi)).2.
move=> A hz; exact (@measure_density_null_set R X phi nu (derivation_measure_law hf) f A hd hz).
Qed.
