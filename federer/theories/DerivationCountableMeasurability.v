(** Federer (1969), 2.9.10, p. 157: continuous/singular derivates and
    independence of the Vitali relation. All scalar values retain partial
    domains. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets cardinality
  reals constructive_ereal topology.
From Federer Require Import MeasureUP MeasureBasic MeasureFiniteClosure
  MeasureDerivationContext CoveringFamilyUP MetricDiameter TopologicalBorel BorelRegularMeasureUP
  BoundedBorelPartitionUP BoundedBorelPartition CountablyMeasurableUP
  CountablyMeasurableBasic CountablyMeasurableUnions.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [derivation_measure_measurable_countably_measurable]:
    supporting sigma-finiteness observation for the L-infinity inclusion in
    Federer 2.9.10, p. 157. Every measurable set for a measure in M is a
    countable union of finite measurable sets: intersect with the bounded
    Borel partition already used in 2.9.2. This infrastructure is not a
    separate claim. *)
Lemma derivation_measure_measurable_countably_measurable (R : realType) (X : metricType R)
    (phi : set X -> \bar R) A :
  is_derivation_measure phi -> measure_measurable phi A -> measure_countably_measurable phi A.
Proof.
move=> hphi hA; have hm := derivation_measure_law hphi.
have [P hP] := @bounded_borel_partition_exists R X.
have he : A=\bigcup_n (A `&` P n).
  apply/seteqP; split=> x.
  - move=> hx.
    have hxP : (\bigcup_n P n) x by rewrite (@bounded_borel_partition_union R X P hP).
    have [n _ hn] := hxP; exists n=> //; by split.
  - by move=> [n _ [hx _]].
rewrite he; apply: (@countably_measurable_countable_union R X nat phi setT _ (countableP _))=> n.
have hPm := @borel_regular_borel_measurable R X phi hm (derivation_measure_borel_regular hphi)
  (P n) (@bounded_borel_partition_borel R X P hP n).
apply: finite_measurable_set_countably_measurable.
- exact (@measure_measurable_intersection R X phi hm A (P n) hA hPm).
- apply: le_lt_trans (@measure_mono R X phi hm (A `&` P n) (P n) (fun x hx => hx.2)) _.
  exact: derivation_measure_bounded_finite hphi (P n) (@bounded_borel_partition_bounded R X P hP n).
Qed.
