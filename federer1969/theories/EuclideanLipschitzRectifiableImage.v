(** Federer (1969), 3.2.15, p. 252, first
    sentence of the proof: coordinate inverse fibres
    are countably rectifiable. This supporting lemma
    splits an arbitrary Euclidean parameter set into
    bounded pieces using the definition in 3.2.14. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets cardinality reals constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric
  LipschitzUP LipschitzBasic PartialFunctionUP PartialFunctionBasic
  PartialFunctionSourceRestriction PartialMetricLipschitz PartialMetricLipschitzLaws
  RectifiableSetUP RectifiableElementary CountablyRectifiableUnions
  CoveringFamilyUP CoveringFamilyLaws MetricClosedBalls MetricBoundedClosureLaws.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [euclidean_lipschitz_bounded_image_rectifiable]:
    the bounded-parameter pieces used in Federer
    3.2.15, p. 252, by 3.2.14(1). The
    finite-set convention also covers source dimension zero. *)
Lemma euclidean_lipschitz_bounded_image_rectifiable (R : realType) m
    (X : metricType R)
    (A : set (inner_metric_space (@euclidean_inner_productP R m)))
    (f : inner_metric_space (@euclidean_inner_productP R m) -> X) :
  metric_set_bounded A -> is_metric_lipschitz A f -> is_m_rectifiable m (f @` A).
Proof.
case: m A f=> [|m] A f hb hf.
- change (finite_set (f @` A)).
  have hsub : A `<=` [set (0 : inner_metric_space (@euclidean_inner_productP R 0))].
    move=> x hx; apply/ffunP=> i; by have := ltn_ord i; rewrite ltn0.
  exact: finite_image (sub_finite_set hsub (finite_set1 _)).
- pose g := partial_function_source_restrict A (partial_function_total f).
  exists g; split.
  + by rewrite /g partial_function_source_restrict_domain partial_function_total_domain setIT.
  + split.
    * have [L [_ hL]] := hf; exists L.
      exact: (proj2 (partial_total_restriction_lipschitz A f L) hL).
    * exact: partial_total_restriction_range.
Qed.

(** Source for [euclidean_lipschitz_image_countably_rectifiable]:
    the countable bounded-parameter decomposition behind
    the first conclusion in the proof of Federer
    3.2.15, p. 252. The source subset is
    arbitrary; no measurability or boundedness is assumed. *)
Theorem euclidean_lipschitz_image_countably_rectifiable (R : realType) m
    (X : metricType R)
    (A : set (inner_metric_space (@euclidean_inner_productP R m)))
    (f : inner_metric_space (@euclidean_inner_productP R m) -> X) :
  is_metric_lipschitz A f -> is_countably_m_rectifiable m (f @` A).
Proof.
move=> [L [hL hLip]].
pose P := inner_metric_space (@euclidean_inner_productP R m).
pose D n := A `&` metric_closed_ball (0 : P) (n%:R : R).
have hD n : metric_set_bounded (D n).
  have hsub : D n `<=` metric_closed_ball (0 : P) (n%:R : R).
    by move=> x hx; exact: hx.2.
  have hball : metric_set_bounded (metric_closed_ball (0 : P) (n%:R : R)).
    apply: covering_closed_ball_bounded; by rewrite ler0n.
  exact: (metric_bounded_subset hsub hball).
have hF n : is_m_rectifiable m (f @` D n).
  apply: euclidean_lipschitz_bounded_image_rectifiable (hD n) _.
  exists L; split=> //.
  have hDA : D n `<=` A by move=> x hx; exact: hx.1.
  exact: (metric_lipschitz_bound_restrict hDA hLip).
have he : f @` A=\bigcup_n (f @` D n).
  apply/seteqP; split=> y.
  - move=> [x hx <-]; pose n := Num.bound (mdist (0 : P) x).
    have hn : mdist (0 : P) x<(n%:R : R) by apply: archi_boundP; exact: mdist_ge0.
    exists n=> //; exists x=> //; split=> //; exact: ltW hn.
  - by move=> [n _ [x [hx _] <-]]; exists x.
rewrite he; apply: countably_rectifiable_countable_union (countableP setT) _=> n _.
exact: rectifiable_countably_rectifiable (hF n).
Qed.
