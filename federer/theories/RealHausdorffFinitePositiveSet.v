(** Federer 2.10.45, pp. 202-203: a supporting positive finite-mass
    test set for every nonnegative real degree. The book only needs the
    numerical interval to be nonempty when the prescribed V is null.
    Reuse the original finite Cantor powers of 2.10.29, p. 195, and
    the positive product probability proved for 3.4.4, p. 318. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology lra.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric
  RealMetricBackground RealHausdorffMeasure RealHausdorffNormalisation
  RealHausdorffDegreeTransport RealHausdorffLipschitz RealPower MetricRealPowerMeasure
  PowerCantorPairUP PowerCantorPair PowerCantorFinitePowers EuclideanSetPowers
  CriticalSharpProductUP CriticalSharpProductPositiveMass CountingInjectionBound.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [real_hausdorff_finite_positive_euclidean_set]: supporting
    coefficient consistency in Federer 2.10.45, pp. 202-203. Every
    real degree k>=0 admits a Euclidean test subset of strictly positive
    finite actual H^k mass. At zero use a point; at positive k use
    q identical original Cantor factors of degree k/q, with q>k. *)
Theorem real_hausdorff_finite_positive_euclidean_set (R : realType)
    (k : R) (hk : (0 <= k)%R) :
    exists q : nat, exists V : set (inner_metric_space (@euclidean_inner_productP R q)),
      0 < @real_hausdorff_measure R _ k hk V /\
      @real_hausdorff_measure R _ k hk V < +oo.
Proof.
case: (eqVneq k 0%R) => [hkzero|hkne].
- subst k; exists 0%N,[set (0%R : inner_metric_space (@euclidean_inner_productP R 0))].
  rewrite real_hausdorff_zero_counting counting_measure_singleton_value.
  split; [exact: ltr01|exact: ltry].
have hkpos : (0 < k)%R by rewrite lt_def hkne hk.
pose q0 := Num.truncn k.
have /andP [_ hkq] := truncn_itv hk.
pose beta := (k/q0.+1%:R)%R.
have hq : (0 < q0.+1%:R :> R)%R by rewrite ltr0n.
have hb : (0 < beta)%R by rewrite /beta divr_gt0.
have hb1 : (beta < 1)%R by rewrite /beta ltr_pdivrMr // mul1r.
have hdegree : (q0.+1%:R*beta)%R = k by rewrite /beta mulrC divfK ?gt_eqF.
have [A [f hPair]] := @power_cantor_pair_exists R 1%R beta (fun _ => 2%N)
  ltr01 hb hb1 (fun _ => leqnn 2%N).
pose V := @euclidean_set_power R q0.+1 A.
have hDegree : (0 <= (0%:R+(q0.+1-0)%:R*beta : R))%R.
  rewrite subn0 add0r; exact: mulr_ge0 (ltW hq) (ltW hb).
have hpositive := @critical_sharp_product_positive_hausdorff R q0.+1 0%N beta
  (fun _ => 2%N) A f hDegree (leq0n _) hb hb1 hPair.
have heSet : @critical_sharp_product_source R q0.+1 0%N A = V.
  apply/seteqP; split=> x hx i; [exact: hx i (leq0n i)|by move=> _; exact: hx i].
have hfinite := @power_cantor_positive_cartesian_power_bound R 1%R beta
  (real_hausdorff_normalisation hk) (fun _ => 2%N) A f q0
  ltr01 hb hb1 (ltW (real_hausdorff_normalisation_positive hk)) hPair.
have hd : (0%:R+(q0.+1-0)%:R*beta : R)%R = k by rewrite subn0 add0r hdegree.
have htransport := @real_hausdorff_measure_equal_degree R
  [the metricType R of inner_metric_space (@euclidean_inner_productP R q0.+1)]
  _ _ hDegree hk hd V.
rewrite heSet htransport in hpositive.
rewrite hdegree in hfinite.
exists q0.+1,V; split; first exact: hpositive.
exact: le_lt_trans hfinite (ltry _).
Qed.
