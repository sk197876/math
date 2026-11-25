(** Federer (1969), 2.2.4, p. 62: positive closed subsets and the final
    nullity argument. We derive these consequences from the local measure
    laws and 2.2.3, including the fact that a countable union of null
    singletons is null. Source context: SeparableMetricBaseConstruction.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets cardinality reals constructive_ereal topology.
From Federer Require Import MeasureUP MeasureBasic MeasureIndexedCover MeasureSplit
  NonnegativeSum BorelRegularMeasureUP BorelRegularApproximation ClosedApproximationUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [countable_null_singletons_null]: supporting uncountability
    step in Federer 2.2.4, p. 62. A countable set with null singletons is
    null by the countable-cover law of 2.1.2. *)
Lemma countable_null_singletons_null (R : realType) (T : choiceType)
    (mu : set T -> \bar R) (hm : is_measure mu) (A : set T) :
  countable A -> (forall x, A x -> mu [set x] = 0) -> mu A = 0.
Proof.
move=> hc hz.
have hcover : A `<=` \bigcup_(x in A) [set x] by move=> x hx; exists x.
have hb := @measure_indexed_cover R T T mu hm A A (fun x => [set x]) hc hcover.
rewrite (nonnegative_sum_zero hz) in hb.
apply/eqP; rewrite eq_le hb /=; exact (@measure_nonnegative R T mu hm A).
Qed.

(** Source for [positive_measurable_closed_subset]: supporting application
    of closed approximation in Federer 2.2.4, p. 62 A finite positive
    measurable set contains a positive closed subset. Approximate with error
    below its measure. *)
Lemma positive_measurable_closed_subset (R : realType) (T : metricType R)
    (mu : set T -> \bar R) (hm : is_measure mu)
    (hr : is_borel_regular_measure mu) (A : set T) :
  measure_measurable mu A -> 0 < mu A -> mu A < +oo ->
  exists C, closed C /\ C `<=` A /\ 0 < mu C.
Proof.
move=> hA hp hf.
have hfin : mu A \is a fin_num by rewrite ge0_fin_numE //; exact: (@measure_nonnegative R T mu hm A).
have he : (0 < fine (mu A))%R by apply: fine_gt0; apply/andP; split.
have [C [hC [hCA herr]]] := @borel_regular_closed_approximation R T mu hm hr A hA hf _ he.
rewrite fineK // in herr.
exists C; split=> //; split=> //.
case: (eqVneq (mu C) 0)=> [hz|hn]; last by rewrite lt_def hn (@measure_nonnegative R T mu hm C).
exfalso.
have hcover : A `<=` C `|` (A `\` C).
  move=> x hx; case: (pselect (C x))=> hc; [by left|right; by split].
have hb := @measure_binary_cover R T mu hm A C (A `\` C) hcover.
rewrite hz add0e in hb; by have := le_lt_trans hb herr; rewrite ltxx.
Qed.

(** Source for [measurable_without_positive_closed_subset_null]: direct
    final implication in Federer 2.2.4, p. 62. *)
Lemma measurable_without_positive_closed_subset_null (R : realType) (T : metricType R)
    (mu : set T -> \bar R) (hm : is_measure mu)
    (hr : is_borel_regular_measure mu) (A : set T) :
  measure_measurable mu A -> mu A < +oo ->
  (forall C, closed C -> C `<=` A -> ~ (0 < mu C)) -> mu A = 0.
Proof.
move=> hA hf hn; case: (eqVneq (mu A) 0)=> [he|he]; first exact he.
have hp : 0 < mu A by rewrite lt_def he (@measure_nonnegative R T mu hm A).
have [C [hC [hCA hpos]]] := positive_measurable_closed_subset hm hr hA hp hf.
exfalso; exact: hn C hC hCA hpos.
Qed.
