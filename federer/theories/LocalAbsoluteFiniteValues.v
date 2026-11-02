(** Finite values almost everywhere under the local hypothesis of Federer
    (1969), 2.9.8, p. 156. The scalar range in that theorem includes
    infinities; finite local absolute integrals exclude them almost
    everywhere. Exhaust by the existing bounded Borel partition and apply
    the finite-integral consequence 2.4.3(4), p. 82, on each piece. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  cardinality reals constructive_ereal topology.
From Federer Require Import ExtendedRealOrderTopology PartialFunctionUP PartialZeroExtension
  MeasureUP MeasureAlmostUP MeasureAlmostBasic MeasurableFunctionUP MeasureIntegralUP
  MeasureDerivationContext BorelRegularMeasureUP BoundedBorelPartitionUP BoundedBorelPartition
  LocalAbsoluteIntegrability MeasureSummableFiniteValues.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [locally_absolutely_integrable_finite_almost]:
    supporting finite-value assertion for recombining the
    two parts in Federer 2.9.8, p. 156.
    Neither total finite mass nor pointwise finiteness
    of the original partial function is assumed. *)
Lemma locally_absolutely_integrable_finite_almost (R : realType) (X : metricType R)
    (phi : set X -> \bar R) (f : partial_function X (extended_real_line R)) :
  is_derivation_measure phi -> is_measure_measurable_function phi f -> is_locally_absolutely_integrable phi f ->
  measure_almost_everywhere phi (partial_extended_finite_locus f).
Proof.
move=> hphi hf hlocal; have hm := derivation_measure_law hphi.
have [P hP] := @bounded_borel_partition_exists R X.
pose F n := partial_function_zero_extension (0 : extended_real_line R) (P n) f.
have hFn n : measure_almost_everywhere phi (partial_extended_finite_locus (F n)).
  have hPm := @borel_regular_borel_measurable R X phi hm (derivation_measure_borel_regular hphi)
    (P n) (bounded_borel_partition_borel hP n).
  have [a [b [_ [_ hi]]]] := @locally_absolutely_integrable_part_values R X phi f hm hf hlocal
    (P n) (bounded_borel_partition_bounded hP n) hPm.
  have hs : is_measure_summable phi (F n) by exists (a-b)%R.
  exact (@measure_summable_finite_almost R X phi hm (F n) hs).
have hall := @measure_almost_everywhere_countable R X _ phi hm setT
  (fun n => partial_extended_finite_locus (F n)) (countableP _) (fun n _ => hFn n).
apply: (@measure_almost_everywhere_mono R X phi hm _ _ _ hall)=> x hx.
have hcover : (\bigcup_n P n) x by rewrite (bounded_borel_partition_union hP).
have [n _ hn] := hcover.
have [y [hy hyfin]] := hx n Logic.I.
exists y; split=> //.
exact: (@partial_function_zero_extension_on X (extended_real_line R) 0 (P n) f x y hn).1 hy.
Qed.
