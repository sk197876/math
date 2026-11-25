(** Federer (1969), 3.2.14, p. 252, first observation:
    the closure of an m rectifiable set is m rectifiable.
    A closed graph over the compact closure of the bounded
    source gives the result in every metric target. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets cardinality reals constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric
  PartialFunctionUP PartialMetricLipschitz RectifiableSetUP
  PartialLipschitzClosureUP PartialLipschitzClosureSealed PartialLipschitzClosureLaws
  MetricBoundedClosureLaws.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [rectifiable_closure]: the assertion
    that Clos S is m rectifiable in Federer 3.2.14,
    p. 252. The finite-set convention covers dimension
    zero; no completeness is added to the target. *)
Theorem rectifiable_closure (R : realType) (X : metricType R) m (E : set X) :
  is_m_rectifiable m E -> is_m_rectifiable m (closure E).
Proof.
case: m=> [|m].
- move=> hE.
  have hc : closed E := (proj1 (@accessible_finite_set_closed X)
    (hausdorff_accessible (@metric_hausdorff R X)) E hE).
  by rewrite -((closure_id E).1 hc).
- move=> [f [hb [[L hL] hr]]].
  pose g := @PartialLipschitzClosure.value R
    (inner_metric_space (@euclidean_inner_productP R m.+1)) X f L hL.
  have hg := @PartialLipschitzClosure.laws R
    (inner_metric_space (@euclidean_inner_productP R m.+1)) X f L hL.
  exists g; split.
  + exact: metric_bounded_subset (partial_lipschitz_closure_domain_subset hg)
      (metric_bounded_closure hb).
  + split.
    * exists L; exact: partial_lipschitz_closure_bound hg hL.
    * rewrite (partial_lipschitz_closure_range hg (euclidean_bounded_closure_compact hb)) hr.
      reflexivity.
Qed.
