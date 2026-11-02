(** Federer (1969), 3.1.16–3.1.17, pp. 228–229: intrinsic predicates
    for finite approximate growth and class-one Lusin approximation.
    These definitions specify assertions; they introduce no project axiom. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets
  reals constructive_ereal topology.
From Federer Require Import Hom GrassmannAbbreviations EuclideanInnerProduct
  InnerNorm InnerMetric EuclideanLebesgueDimensions NormClassHigherUP
  CenteredBallRelations ApproximateMetricGrowth MeasureApproximateOrderLimits.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [finite_approximate_growth_points]: the points satisfying
    the growth hypothesis in Federer 3.1.16, p. 228, and the converse
    discussed in 3.1.17, p. 229. The quotient is defined on the punctured
    actual domain, including the erratum convention of 2.9.12. *)
Definition finite_approximate_growth_points (R : realType) m n
    (A : set (inner_metric_space (@euclidean_inner_productP R m)))
    (f : inner_metric_space (@euclidean_inner_productP R m)->
      inner_metric_space (@euclidean_inner_productP R n)) :=
  [set a | (measure_approximate_upper_limit (@euclidean_lebesgue_measure R m)
    (@centered_closed_ball_relation R [the metricType R of inner_metric_space (@euclidean_inner_productP R m)])
    (partial_metric_growth_quotient A f a) a< +oo)%E].

(** Source for [has_class_one_lusin_approximation]: the conclusion of
    Federer 3.1.16, p. 228, referred to in 3.1.17, p. 229. For each
    positive tolerance a global class-one map agrees outside an exceptional
    subset of A of smaller measure. No measurability of A is built into
    this predicate, so its role in the converse remains explicit. *)
Definition has_class_one_lusin_approximation (R : realType) m n
    (Z : nat->lmodType R)
    (ev : forall i, {ffun 'I_i->R_n R m}->Hom (Z i) (R_n R n))
    (ZN : forall i, Z i->R)
    (A : set (inner_metric_space (@euclidean_inner_productP R m)))
    (f : inner_metric_space (@euclidean_inner_productP R m)->
      inner_metric_space (@euclidean_inner_productP R n)) :=
  forall e : R, 0<e -> exists g,
    norm_class_higher (inner_norm (@euclidean_inner_productP R m))
      (inner_norm (@euclidean_inner_productP R n)) ev ZN (fun _=>True) g 1%N /\
    (@euclidean_lebesgue_measure R m (A `\` [set x | f x=g x])<e%:E)%E.
