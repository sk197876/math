(** Concrete converse counterexample for Federer (1969), 2.3.8, p. 78.
    Enumerate all binary-prefix cylinders without repetition and take their
    characteristic functions. Cylinder costs tend to zero, but every point
    lies in arbitrarily late cylinders. This binary-product version uses a
    locally constructed finite measure and proves its nontriviality and
    event measurability. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric PartialFunctionUP PartialFunctionBasic PartialFunctionLimitUP
  MeasureUP MeasureAlmostUP MeasureGauge MeasureGaugeCharacteristic MeasureConvergenceUP MeasureTotalDistance
  MeasurableNormedFunctionUP MeasurableNormedCharacteristic MeasurableNormedBasic
  CharacteristicFunctionUP CharacteristicFunctionSealed BinarySequenceCylinders BinaryCylinderCost
  BinaryCylinderEnvelope BinaryWordEnumerationUP BinaryWordEnumerationSealed BinaryWordEnumerationLaws BinaryCylinderSmallCost.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [binary_typewriter]: local characteristic-function sequence
    witnessing the false converse in Federer 2.3.8, p. 78 *)
Definition binary_typewriter (R : realType) n : binary_sequence_space -> real_norm_metric_space (scalar_absolute_value_norm R) :=
  @CharacteristicFunction.value R binary_sequence_space (binary_cylinder (BinaryWordEnumeration.decode n)).

(** Source for [binary_typewriter_characteristic]: each term
    satisfies the characteristic-function laws, supporting the
    counterexample in Federer 2.3.8, p. 78. *)
Lemma binary_typewriter_characteristic (R : realType) n :
  is_characteristic_function (binary_cylinder (BinaryWordEnumeration.decode n)) (@binary_typewriter R n).
Proof. exact: CharacteristicFunction.laws. Qed.

(** Source for [binary_typewriter_measurable_normed]: each term
    belongs to A(mu,R), including the essential-separability
    condition, in the local counterexample to Federer 2.3.8,
    p. 78. *)
Lemma binary_typewriter_measurable_normed (R : realType) n :
  @is_measurable_normed_function R [the choiceType of binary_sequence_space] R^o _
    (scalar_absolute_value_norm R) (@binary_cylinder_measure R)
    (partial_function_total (@binary_typewriter R n)).
Proof.
exact (@measurable_normed_characteristic R [the choiceType of binary_sequence_space] _
  (binary_cylinder_measure_is_measure R) _ _ (binary_typewriter_characteristic R n)
  (binary_cylinder_measurable R _)).
Qed.

(** Source for [binary_typewriter_gauge]: the gauge is bounded
    by the cylinder cost in the local example for Federer
    2.3.8, p. 78, using his characteristic formula. *)
Lemma binary_typewriter_gauge (R : realType) n :
  measure_gauge (@binary_cylinder_measure R) (fun y : R => `|y|%R)
    (partial_function_total (@binary_typewriter R n)) <=
    @binary_cylinder_cost R (BinaryWordEnumeration.decode n).
Proof.
have hs := binary_typewriter_characteristic R n.
have he := @measure_gauge_two_value_norm R [the choiceType of binary_sequence_space] R
  _ (binary_cylinder_measure_is_measure R) (fun y : R => `|y|%R)
  (@binary_typewriter R n) (binary_cylinder (BinaryWordEnumeration.decode n)) 1%R ler01.
have hon x : binary_cylinder (BinaryWordEnumeration.decode n) x -> `|binary_typewriter R n x|%R = 1%R.
  move=> hx; by rewrite (characteristic_on_set hs hx) normr1.
have hoff x : ~ binary_cylinder (BinaryWordEnumeration.decode n) x -> `|binary_typewriter R n x|%R = 0%R.
  move=> hx; by rewrite (characteristic_off_set hs hx) normr0.
rewrite (he hon hoff); apply: le_trans _ (binary_cylinder_measure_bound R _).
by rewrite ge_min lexx orbT.
Qed.

(** Source for [binary_typewriter_converges_in_measure]: the
    sequence tends to zero in the pseudometric of Federer
    2.3.8, p. 78, since eventually all prefix lengths
    are large and their assigned measures are small. *)
Theorem binary_typewriter_converges_in_measure (R : realType) :
  @converges_in_measure R [the choiceType of binary_sequence_space] R^o (@binary_cylinder_measure R) (fun y : R => `|y|%R)
    (fun n => partial_function_total (@binary_typewriter R n))
    (partial_function_total (fun _ : binary_sequence_space => (0%R : real_norm_metric_space (scalar_absolute_value_norm R)))).
Proof.
move=> e he.
have [K hK] := @binary_enumeration_cost_tends_zero R BinaryWordEnumeration.encode BinaryWordEnumeration.decode
  BinaryWordEnumeration.laws e he.
exists K=> n hn.
rewrite (@measure_total_distance_zero R [the choiceType of binary_sequence_space] R^o _
  (binary_cylinder_measure_is_measure R)).
exact: le_lt_trans (binary_typewriter_gauge R n) (hK n hn).
Qed.

(** Source for [binary_typewriter_not_pointwise_zero]: at every source point
    the characteristic sequence takes value one at arbitrarily late indices,
    so it cannot converge to zero. This validates the false converse in
    Federer 2.3.8, p. 78. *)
Theorem binary_typewriter_not_pointwise_zero (R : realType) x :
  ~ partial_function_limit_locus (fun n => partial_function_total (@binary_typewriter R n))
    (partial_function_total (fun _ : binary_sequence_space => (0%R : real_norm_metric_space (scalar_absolute_value_norm R)))) x.
Proof.
move=> [u [z [hu [hz hlim]]]].
pose M := real_norm_metric_space (scalar_absolute_value_norm R).
have hnb : nbhs z [set y : M | (mdist z y < 1)%R].
  apply: (proj2 (metricType_numDomainType.nbhs_mdistP z _)); exists 1%R; first exact: ltr01.
  by move=> y hy.
have [K _ hK] := hlim _ hnb.
have [n [hn hxn]] := @binary_enumeration_late_membership BinaryWordEnumeration.encode BinaryWordEnumeration.decode
  BinaryWordEnumeration.laws x K.
have hv : u n = (1%R : M).
  rewrite -(hu n).
  exact (@characteristic_on_set R binary_sequence_space _ (@binary_typewriter R n)
    (binary_typewriter_characteristic R n) x hxn).
have ht : (mdist z (u n) < 1)%R := hK n hn.
by rewrite -hz hv real_norm_metric_distanceE sub0r normrN normr1 ltxx in ht.
Qed.

(** Source for [binary_typewriter_not_almost_zero]: the source
    has measure one and the zero-limit locus is empty; hence
    convergence in measure does not imply almost-everywhere
    convergence to the same limit, Federer 2.3.8, p. 78. *)
Theorem binary_typewriter_not_almost_zero (R : realType) :
  ~ measure_almost_everywhere (@binary_cylinder_measure R)
    (partial_function_limit_locus (fun n => partial_function_total (@binary_typewriter R n))
      (partial_function_total (fun _ : binary_sequence_space => (0%R : real_norm_metric_space (scalar_absolute_value_norm R))))).
Proof.
have he : partial_function_limit_locus (fun n => partial_function_total (@binary_typewriter R n))
    (partial_function_total (fun _ : binary_sequence_space => (0%R : real_norm_metric_space (scalar_absolute_value_norm R)))) = set0.
  apply/seteqP; split=> x; last by [].
  exact: binary_typewriter_not_pointwise_zero R x.
rewrite /measure_almost_everywhere he setC0 binary_cylinder_measure_whole.
by move=> /eqP; rewrite onee_eq0.
Qed.
