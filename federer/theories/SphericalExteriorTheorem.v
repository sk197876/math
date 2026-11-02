(** Federer (1969), 2.10.39, printed p. 199: spherical measure is at most
    n^(m/2) 2^(m-1) times exterior-diameter measure. The degree m is a
    positive integer as in 2.10.3, pp. 171–172; that definition does not
    restrict m to n. Include degrees above dimension by the proved Hausdorff
    dimension-drop and spherical comparison laws. Source context and
    covering background: SphericalExteriorComparison.v and
    EuclideanAboveDimensionNull.v. *)
From mathcomp Require Import all_boot all_order all_algebra reals classical_sets constructive_ereal topology.
From Federer Require Import EuclideanInnerProduct InnerMetric HausdorffMeasure
  ExteriorMeasure MeasureUP SphericalExteriorComparison EuclideanAboveDimensionNull.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [spherical_exterior_measure_bound]: direct
    corollary 2.10.39, p. 199, for every positive
    natural degree and every Euclidean target. Write
    n^(m/2) as sqrt(n)^m, include m>n and
    ambient dimension zero, and impose no measurability,
    finite-mass or boundedness hypothesis on the target. *)
Theorem spherical_exterior_measure_bound (R : realType) n m
    (A : set (inner_metric_space (@euclidean_inner_productP R n))) :
  (0<m)%N ->
  (@spherical_measure R
    [the metricType R of inner_metric_space (@euclidean_inner_productP R n)] m A<=
    ((Num.sqrt n%:R)^+m*2^+m.-1)%:E*@exterior_diameter_measure R n m A)%E.
Proof.
case: m=> [|p] hm; first by rewrite ltn0 in hm.
case: (leqP p.+1 n)=> hpn.
- exact: (@euclidean_spherical_exterior_comparison R n p hpn A).
- rewrite (@euclidean_spherical_above_dimension_zero R n p.+1 A hpn).
  apply: mule_ge0.
  + rewrite lee_fin; apply: mulr_ge0; apply: exprn_ge0.
    * exact: sqrtr_ge0.
    * exact: ler0n.
  + exact (@measure_nonnegative R
      [the choiceType of inner_metric_space (@euclidean_inner_productP R n)]
      (@exterior_diameter_measure R n p.+1)
      (exterior_diameter_measure_is_measure R n p.+1) A).
Qed.

(** Source for [federer_2_10_39]: numbered public alias
    for corollary 2.10.39, p. 199, including
    above-ambient positive degrees and arbitrary targets. *)
Definition federer_2_10_39 := @spherical_exterior_measure_bound.
