(** Supporting Federer (1969), 2.10.14, p. 177: separate the nonatomic
    image-cost contribution from the countable arc-length atoms. This is a
    consequence of measurable splitting, 2.1.2, pp. 53–54, and disjoint
    summation, 2.1.6(2), p. 59, rather than an additional statement printed
    in 2.10.14. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  cardinality reals constructive_ereal topology.
From Federer Require Import RealMetricBackground MeasureUP MeasureBasic MeasureSplit
  MeasureAlmostBasic MeasureDisjointSupport NonnegativeSum NonnegativeSumSupport
  NonnegativeSumRestriction BVCurveBorel TopologicalBorel BorelRegularMeasureUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [metric_singleton_sum_bound]: supporting sum of
    arc-length atoms in 2.10.14, p. 177, using the arbitrary
    disjoint-family bound of 2.1.6(2), p. 59. *)
Lemma metric_singleton_sum_bound (R : realType) (X : metricType R)
    (nu : set X -> \bar R) (A : set X) : is_measure nu ->
  is_borel_regular_measure nu -> nonnegative_sum A (fun x => nu [set x])<=nu A.
Proof.
move=> hn hr.
apply: (measure_disjoint_sum_bound hn).
- by move=> x hx y ->.
- move=> x hx; apply: (borel_regular_borel_measurable hn hr).
  exact: countable_metric_set_borel (countable1 x).
- move=> x y hx hy hne; apply/seteqP; split=> // z [-> hyx].
  exfalso; apply: hne; exact: hyx.
Qed.

(** Source for [metric_diffuse_atomic_sum_bound]: supporting
    diffuse-plus-jumps bound in 2.10.14, p. 177. A measure
    vanishing on singletons cannot charge a countable exceptional
    set; its remaining mass and the dominating measure's atoms
    fit in the two measurable parts of A. *)
Theorem metric_diffuse_atomic_sum_bound (R : realType) (X : metricType R)
    (mu nu : set X -> \bar R) (A D : set X) :
  is_measure mu -> is_measure nu -> is_borel_regular_measure nu ->
  (forall B, mu B<=nu B) -> (forall x, mu [set x]=0) ->
  countable D -> (forall x, ~D x -> nu [set x]=0) ->
  mu A+nonnegative_sum A (fun x => nu [set x])<=nu A.
Proof.
move=> hm hn hr hdom hz hD hatom.
have hsing : mu D=0.
  have he : D=\bigcup_(x in D) [set x].
    apply/seteqP; split; first by move=> x hx; exists x.
    by move=> x [y hy ->].
  rewrite he; exact (@measure_null_countable_union R X
    X mu hm D (fun x => [set x]) hD (fun x hx => hz x)).
have hzero : mu (A `&` D)=0.
  apply: (@measure_null_subset R X mu hm (A `&` D) D); last exact hsing.
  by move=> x [hx hd].
have hcover : A `<=` (A `\` D) `|` (A `&` D).
  move=> x hx; case: (pselect (D x))=> hd; [right|left]; by split.
have hdiff : mu A<=nu (A `\` D).
  have hh := measure_binary_cover hm hcover.
  rewrite hzero adde0 in hh; exact: le_trans hh (hdom _).
have hsum : nonnegative_sum A (fun x => nu [set x])<=nu (A `&` D).
  rewrite (@nonnegative_sum_split R X A D
    (fun x => nu [set x]) (fun x hx => measure_nonnegative hn _)).
  have he : nonnegative_sum (A `\` D) (fun x => nu [set x])=0.
    apply: nonnegative_sum_zero=> x [hx hd]; exact: hatom x hd.
  rewrite he adde0; exact: metric_singleton_sum_bound hn hr.
have hmeas : measure_measurable nu D.
  apply: (borel_regular_borel_measurable hn hr); exact: countable_metric_set_borel hD.
apply: le_trans (leeD hdiff hsum) _.
by rewrite addeC -(hmeas A).
Qed.
