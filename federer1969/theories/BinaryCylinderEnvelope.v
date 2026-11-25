(** The binary-cylinder covering measure for a concrete counterexample to
    Federer (1969), 2.3.8, p. 78. The covering infimum of 2.10.1, p. 170, is
    accessed through its sealed laws. The proof of total mass one reduces a
    countable cylinder cover to a finite cover using general-topology
    compactness, then applies finite counting. *)
From mathcomp Require Import all_boot all_order all_algebra finmap classical_sets cardinality
  reals constructive_ereal topology.
From Federer Require Import NonnegativeSum MeasureUP CountableCoverEnvelopeUP
  CountableCoverEnvelopeBasic CountableCoverEnvelopeLaws CountableCoverEnvelopeSealed
  CountableCoverMeasurability BinaryCylinderSplitCost CompactFiniteCover BinarySequenceCylinders BinaryCylinderCost BinaryCylinderFiniteCover.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope fset_scope.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [binary_cylinder_measure]: the local covering
    measure witnessing the counterexample to Federer 2.3.8,
    p. 78, defined by the sealed infimum interface from
    2.10.1, p. 170. *)
Definition binary_cylinder_measure (R : realType) :=
  @CountableCoverEnvelope.value R [the choiceType of binary_sequence_space]
    [the choiceType of (seq bool : Type)] binary_cylinder (@binary_cylinder_cost R).

(** Source for [binary_cylinder_measure_envelope]: abstract
    covering-infimum laws for the local example supporting Federer
    2.3.8, p. 78. *)
Lemma binary_cylinder_measure_envelope (R : realType) :
  is_countable_cover_envelope binary_cylinder (@binary_cylinder_cost R) (@binary_cylinder_measure R).
Proof. exact: CountableCoverEnvelope.laws. Qed.

(** Source for [binary_cylinder_measure_is_measure]: the
    cylinder covering infimum measures the binary product, by
    Federer 2.10.1, p. 170, supporting 2.3.8. *)
Lemma binary_cylinder_measure_is_measure (R : realType) : is_measure (@binary_cylinder_measure R).
Proof.
apply: countable_cover_envelope_is_measure (binary_cylinder_measure_envelope R) _=> w.
exact: ltW (binary_cylinder_cost_positive R w).
Qed.

(** Source for [binary_cylinder_measure_bound]: every cylinder
    has measure at most its assigned cost, supporting the small
    characteristic-function gauges in the local Federer 2.3.8 example. *)
Lemma binary_cylinder_measure_bound (R : realType) w :
  binary_cylinder_measure R (binary_cylinder w) <= (@binary_cylinder_cost R w).
Proof.
exact (@countable_cover_envelope_generator_bound R [the choiceType of binary_sequence_space]
  [the choiceType of (seq bool : Type)] binary_cylinder (@binary_cylinder_cost R) _
  (binary_cylinder_measure_envelope R) w (ltW (binary_cylinder_cost_positive R w))).
Qed.

(** Source for [binary_cylinder_measure_whole]: the covering
    measure has total mass exactly one, validating the nontrivial
    finite source of the local counterexample to Federer 2.3.8,
    p. 78. Compactness supplies the finite subcover needed
    by the elementary counting lower bound. *)
Theorem binary_cylinder_measure_whole (R : realType) : binary_cylinder_measure R setT = 1.
Proof.
apply/eqP; rewrite eq_le; apply/andP; split.
- rewrite -binary_cylinder_empty_word.
  apply: le_trans (binary_cylinder_measure_bound R [::]) _.
  by rewrite binary_cylinder_cost_empty_word.
- apply: (countable_cover_envelope_greatest (binary_cylinder_measure_envelope R))=> G _ hc.
  have [F hF hcov] := @compact_open_finite_cover [the topologicalType of binary_sequence_space]
    [the choiceType of (seq bool : Type)] G binary_cylinder setT binary_sequence_compact
    (fun w _ => binary_cylinder_open w) hc.
  apply: le_trans (binary_finite_cylinder_cover_cost R hcov) _.
  apply: nonnegative_sum_subset=> w hw; exact (set_mem (hF w hw)).
Qed.

(** Source for [binary_cylinder_measurable]: every binary cylinder
    is measurable for the constructed measure, completing the
    finite-prefix events used in the local counterexample to
    Federer 2.3.8, p. 78. The proof uses the
    Caratheodory splitting definition of 2.1.2, p. 54. *)
Theorem binary_cylinder_measurable (R : realType) a :
  measure_measurable (@binary_cylinder_measure R) (binary_cylinder a).
Proof.
apply: (@countable_cover_generator_split_measurable R [the choiceType of binary_sequence_space]
  [the choiceType of (seq bool : Type)] binary_cylinder (@binary_cylinder_cost R) _
  (binary_cylinder_measure_envelope R) (fun w => ltW (binary_cylinder_cost_positive R w)) (binary_cylinder a)).
move=> w; exact: (@binary_cylinder_split_cost R _ (binary_cylinder_measure_is_measure R)
  (binary_cylinder_measure_bound R) w a).
Qed.
