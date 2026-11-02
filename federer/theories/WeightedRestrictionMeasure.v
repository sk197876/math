(** Federer (1969), 2.10.24, p. 188, final paragraph: supporting measure
    associated with restricting a fixed nonnegative input before taking the
    limiting weighted functional. The measure laws of 2.1.2, pp. 53–54,
    follow from increasingly fine cover assembly, not from a
    countable-subadditivity assertion at a fixed cutoff. The value has its
    own abstract supremum specification, proved existence witness and opaque
    seal. Evaluation through the existing limiting functional is derived
    from the two specifications, not from the witness. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  cardinality reals constructive_ereal topology.
From Federer Require Import WeightedCountableSubadditivity WeightedMetricLimitUP
  WeightedMetricLimitLaws WeightedMetricLimit CaratheodoryLimitUP CaratheodoryLimitMeasure
  WeightedRestrictionMeasureLaws WeightedRestrictionMeasureSealed
  MeasureUP MeasureAlmostUP MeasureAlmostBasic CountableCostEnumeration
  NonnegativeSum NonnegativeSumSupport.
From Federer Require Export WeightedRestrictionMeasureUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [weighted_restriction_measure]: supporting measure
    for 2.10.24, p. 188, exposed only through its
    sealed supremum specification. Measure and evaluation
    laws are proved separately from that specification;
    the desired integral equality is not assumed. *)
Definition weighted_restriction_measure (R : realType) (X : metricType R) (J : choiceType)
    (S : J -> set X) (c : J -> \bar R) (psi : set X -> \bar R)
    (f : X -> \bar R) (A : set X) :=
  @WeightedRestrictionMeasure.value R X J S c psi f A.

(** Source for [weighted_restriction_measure_specification]: supporting
    abstract positive-cutoff supremum laws for the auxiliary
    measure in 2.10.24, p. 188. No implementation is
    exposed by the public interface. *)
Lemma weighted_restriction_measure_specification (R : realType) (X : metricType R) (J : choiceType)
    (S : J -> set X) (c : J -> \bar R) (psi : set X -> \bar R) (f : X -> \bar R) :
  is_weighted_restriction_measure S c psi f (weighted_restriction_measure S c psi f).
Proof. exact: WeightedRestrictionMeasure.laws. Qed.

(** Source for [weighted_restriction_measureE]: supporting evaluation
    for the auxiliary measure in 2.10.24, p. 188.
    The two abstract supremum specifications prove this
    identity, independently of either hidden witness. *)
Lemma weighted_restriction_measureE (R : realType) (X : metricType R) (J : choiceType)
    (S : J -> set X) (c : J -> \bar R) (psi : set X -> \bar R) (f : X -> \bar R) A :
  weighted_restriction_measure S c psi f A=
    weighted_metric_limit S c psi (weighted_function_restriction f A).
Proof.
exact: weighted_restriction_limit_value (weighted_restriction_measure_specification S c psi f)
  (weighted_metric_limit_specification S c psi) A.
Qed.

(** Source for [weighted_restriction_measure_empty]: supporting
    empty-value law for the auxiliary measure in the
    final paragraph of 2.10.24, p. 188. An empty
    restriction is the total zero function, including
    when the original input has infinite values. *)
Lemma weighted_restriction_measure_empty (R : realType) (X : metricType R) (J : choiceType)
    (S : J -> set X) (c : J -> \bar R) (psi : set X -> \bar R) (f : X -> \bar R) :
  is_measure psi -> weighted_restriction_measure S c psi f set0=0.
Proof.
move=> hm; rewrite weighted_restriction_measureE.
have he : weighted_function_restriction f set0=(fun _=>0).
  by apply: funext=> x; rewrite /weighted_function_restriction in_set0.
rewrite he; exact: weighted_metric_limit_zero hm (weighted_metric_limit_specification S c psi).
Qed.

(** Source for [weighted_restriction_is_measure]: supporting
    outer-measure laws of 2.1.2, pp. 53–54, for
    the final-paragraph argument in 2.10.24, p. 188.
    Countable family enumeration preserves the total cost
    and uses the empty restriction as a zero-cost
    default. The original input need not be measurable. *)
Theorem weighted_restriction_is_measure (R : realType) (X : metricType R) (J : choiceType)
    (S : J -> set X) (c : J -> \bar R) (psi : set X -> \bar R) (f : X -> \bar R) :
  is_caratheodory_limit S c psi -> (forall j, 0<=c j) -> (forall x, 0<=f x) ->
  is_measure (weighted_restriction_measure S c psi f).
Proof.
move=> hpsi hc hf0.
have hm := caratheodory_limit_is_measure hpsi hc.
pose nu := weighted_restriction_measure S c psi f.
have hnon A : 0<=nu A.
  rewrite /nu weighted_restriction_measureE.
  exact: (@weighted_metric_limit_nonnegative R X J S c psi _
    (weighted_metric_limit_specification S c psi) (weighted_function_restriction f A)).
constructor; first exact hnon.
move=> A H hH hAH.
have [B [hB [honto hsum]]] := @countable_zero_cost_enumeration R
  [the choiceType of (set X)] H nu set0 hH
  (@weighted_restriction_measure_empty R X J S c psi f hm) (fun C _=>hnon C).
have hdom : measure_almost_everywhere psi [set x | weighted_function_restriction f A x<=
    nonnegative_sum setT (fun n=>weighted_function_restriction f (B n) x)].
  apply: (@measure_almost_everywhere_mono R X psi hm setT _ _
    (measure_almost_everywhere_true hm))=> x _.
  change (is_true (weighted_function_restriction f A x<=
    nonnegative_sum setT (fun n=>weighted_function_restriction f (B n) x))).
  rewrite /weighted_function_restriction; case hx: (x \in A); last exact: nonnegative_sum_nonnegative.
  have [C hC hxC] := hAH x (set_mem hx).
  have [n hn] := honto C hC.
  have hb := @nonnegative_sum_term R [the choiceType of (nat : Type)] setT
    (fun k=>if x \in B k then f x else 0) n Logic.I.
  by rewrite hn (mem_set hxC) in hb.
have hh := @weighted_limit_countable_subadditivity R X J S c psi
  (weighted_function_restriction f A) (fun n=>weighted_function_restriction f (B n)) hpsi hc hdom.
have he : (fun n=>weighted_metric_limit S c psi (weighted_function_restriction f (B n)))=
    (fun n=>nu (B n)).
  apply: funext=> n; by rewrite /nu weighted_restriction_measureE.
rewrite he -weighted_restriction_measureE in hh.
change (is_true (nu A<=nonnegative_sum H nu)).
by rewrite hsum in hh.
Qed.
