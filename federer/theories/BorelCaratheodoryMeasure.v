(** The Borel-generator specialization of Federer (1969), 2.10.1, p. 170,
    used in 2.10.8, p. 175, and 2.10.10, p. 176. The implementation remains
    behind the existing generic Caratheodory seal; the covering cost is used
    through its proved laws. Source context: BorelCoverCostUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets
  reals constructive_ereal topology.
From Federer Require Import MeasureUP BorelRegularMeasureUP TopologicalBorel
  BorelCoverCostUP CaratheodoryLimitUP CaratheodoryMeasure
  MetricScaleEnvelopeUP MetricScaleEnvelope.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [borel_caratheodory_measure]: the measure
    constructed from the Borel-family cost in Federer
    2.10.8, p. 175, through the sealed
    general construction of 2.10.1, p. 170. *)
Definition borel_caratheodory_measure (R : realType) (X : metricType R)
    (c : set X -> \bar R) :=
  @caratheodory_measure R X (@borel_metric_sets R X) (fun j => val j) (fun j => c (val j)).

(** Source for [borel_caratheodory_specification]: the
    covering-infimum/supremum laws of Federer 2.10.1,
    p. 170, for the Borel family of 2.10.8,
    p. 175. *)
Lemma borel_caratheodory_specification (R : realType) (X : metricType R)
    (c : set X -> \bar R) :
  is_caratheodory_limit (fun j : @borel_metric_sets R X => val j)
    (fun j => c (val j)) (borel_caratheodory_measure c).
Proof. exact: caratheodory_measure_specification. Qed.

(** Source for [borel_caratheodory_is_measure]: the
    measure law in Federer 2.10.1, p. 170,
    for the construction of 2.10.8, p. 175. *)
Lemma borel_caratheodory_is_measure (R : realType) (X : metricType R)
    (c : set X -> \bar R) : is_borel_cover_cost c ->
  is_measure (borel_caratheodory_measure c).
Proof.
move=> hc; apply: caratheodory_measure_is_measure=> j.
exact (@borel_cover_cost_nonnegative R X c hc (val j) (set_valP j)).
Qed.

(** Source for [borel_caratheodory_borel_regular]: the
    Borel regularity assertion in Federer 2.10.1,
    p. 170, used for the Borel-partition theorem
    2.10.8, p. 175. *)
Lemma borel_caratheodory_borel_regular (R : realType) (X : metricType R)
    (c : set X -> \bar R) : is_borel_cover_cost c ->
  is_borel_regular_measure (borel_caratheodory_measure c).
Proof.
move=> hc; apply: caratheodory_measure_borel_regular.
- move=> j; exact (@borel_cover_cost_nonnegative R X c hc (val j) (set_valP j)).
- move=> j; exact: set_valP j.
Qed.

(** Source for [borel_caratheodory_cost_bound]: the
    opening inequality zeta(S)<=psi(S) in the proof
    of Federer 2.10.8, p. 175, on every
    Borel set. It follows from the covering law for
    the cost at any one positive diameter cutoff. *)
Lemma borel_caratheodory_cost_bound (R : realType) (X : metricType R)
    (c : set X -> \bar R) : is_borel_cover_cost c ->
  forall A, borel_set A -> c A<=borel_caratheodory_measure c A.
Proof.
move=> hc A hA.
pose J := @borel_metric_sets R X.
pose S := fun j : J => val j.
pose d := fun j : J => c (val j).
pose nu := metric_scale_envelope S d 1.
have hn := @metric_scale_envelope_specification R X J S d 1.
have hlow : c A<=nu A.
  apply: (metric_scale_envelope_greatest hn)=> G hG _ hcov.
  apply: (@borel_cover_cost_cover R X c hc J G S A hG hA _ hcov)=> j hj.
  exact: set_valP j.
apply: le_trans hlow _.
exact (@caratheodory_limit_upper R X J S d (borel_caratheodory_measure c)
  (borel_caratheodory_specification c) A 1 nu lte01 hn).
Qed.
