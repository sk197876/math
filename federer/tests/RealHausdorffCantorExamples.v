(** Boundary regressions for the Gamma-normalized measure connection in
    Federer 2.10.28, pp. 191-193. The half-degree example uses the original
    binary schedule and the actual Gamma coefficient. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets
  reals constructive_ereal topology lra.
From Federer Require Import RealMetricBackground RealPower
  RealHausdorffNormalisation RealHausdorffMeasure RealHausdorffCantorPair
  ConcaveIntervalMeasure PowerCantorPairUP PowerCantorPair CountingMeasure.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [zero_degree_interval_counting_regression]: boundary
    regression for the cover-measure identification used in Federer
    2.10.28, pp. 191-193, and the counting convention of 2.10.2, p. 171.
    The canonical degree-zero interval measure is counting measure on
    every subset, including infinite sets. *)
Theorem zero_degree_interval_counting_regression (R : realType)
    (A : set (real_line_metric R)) :
    concave_interval_measure
      (fun t => real_hausdorff_normalisation (lexx (0 : R))*real_power t 0) A=
    @counting_measure R [the metricType R of real_line_metric R] A.
Proof.
rewrite -real_hausdorff_interval_power_agreement.
exact: real_hausdorff_zero_counting.
Qed.

(** Source for [half_degree_cantor_hausdorff_regression]: concrete
    noninteger-degree regression for Federer 2.10.28, p. 193. The binary
    power Cantor pair has its original cumulative function and exactly
    alpha(1/2)*2^(-1/2) Hausdorff mass. The coefficient comes from the
    proved Euler-Gamma normalization; no arbitrary normalizer remains. *)
Theorem half_degree_cantor_hausdorff_regression (R : realType)
    (hhalf : (0<1/2 :> R)) :
    let hp := ltW hhalf in
    let c := real_hausdorff_normalisation hp in
    exists A f,
      is_power_cantor_pair c (1/2 : R) (fun _ => 2%N) A f /\
      @real_hausdorff_measure R [the metricType R of real_line_metric R]
        (1/2 : R) hp A=c%:E /\
      (forall x : R,
        @real_hausdorff_measure R [the metricType R of real_line_metric R]
          (1/2 : R) hp (A `&` [set z | z<=x])=(f x)%:E).
Proof.
move=> hp c.
have hc : 0<c := real_hausdorff_normalisation_positive hp.
have hhalf1 : (1/2<1 :> R) by lra.
have [A [f hpair]] := @power_cantor_pair_exists R c (1/2 : R)
  (fun _ => 2%N) hc hhalf hhalf1 (fun _ => leqnn 2).
exists A,f; split=> //.
exact: (@power_cantor_pair_hausdorff_mass R (1/2 : R) hp
  (fun _ => 2%N) A f hhalf hhalf1 hpair).
Qed.
