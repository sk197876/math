(** Federer (1969), 2.4.12, p. 87: private finite Borel approximation
    witness on a closed separable linear subspace. The proof composes sealed
    Borel range reduction, a dense sequence starting at zero, and finite
    nearest-prefix partitions. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets cardinality reals topology.
From Federer Require Import RealNormUP NormMetric ModuleQuotient MetricSubsetBackground
  BorelFunctionUP BorelFunctionBasic ClosedSubsetBorelRetractionUP ClosedSubsetBorelRetractionSealed
  SeparablePointSequenceUP SeparablePointSequenceSealed FiniteNearestApproximationUP
  FiniteNearestApproximation FiniteNearestApproximationSealed SeparableFiniteApproximationUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [separable_finite_approximation_exists]: supporting finite
    Borel approximation existence for Federer 2.4.12, p. 87 Nearest points
    in finite prefixes give both finite images and the pointwise majorant
    needed for powered-error bounded convergence. *)
Theorem separable_finite_approximation_exists (R : realType) (V : lmodType R)
    (N : V -> R) (hN : is_real_norm N) (Z : subspace V)
    (D : set (metric_subset (fun x : real_norm_metric_space hN => Z x))) :
  closed (fun x : real_norm_metric_space hN => Z x) -> countable D -> dense D ->
  exists a, @is_separable_finite_approximation R V N hN Z a.
Proof.
move=> hZ hc hd.
pose S : set (real_norm_metric_space hN) := fun x => Z x.
pose z0 : metric_subset S := @exist (real_norm_metric_space hN) (fun x => x \in S) 0 (mem_set (subspace_zero Z)).
pose r := @ClosedSubsetBorelRetraction.value R [the metricType R of real_norm_metric_space hN] S z0 hZ.
have hr := @ClosedSubsetBorelRetraction.laws R [the metricType R of real_norm_metric_space hN] S z0 hZ.
pose y := @SeparablePointSequence.value R [the metricType R of metric_subset S] z0 D hc hd.
have hy := @SeparablePointSequence.laws R [the metricType R of metric_subset S] z0 D hc hd.
pose q := @FiniteNearestApproximation.value R [the metricType R of metric_subset S] y.
have hq := @FiniteNearestApproximation.laws R [the metricType R of metric_subset S] y.
pose a n x := (val (y (q n (r x))) : real_norm_metric_space hN).
exists a; constructor.
- move=> n.
  have hnear := @finite_nearest_map_borel R [the metricType R of metric_subset S] y q hq n.
  have hincl := continuous_borel_function (@metric_subset_inclusion_continuous R [the metricType R of real_norm_metric_space hN] S).
  exact (borel_function_composition (borel_function_composition hr.1 hnear) hincl).
- move=> n.
  apply: (sub_finite_set (B:= (fun z : metric_subset S => (val z : real_norm_metric_space hN)) @`
    ((fun z => y (q n z)) @` setT))).
  + move=> x [w _ <-]; exists (y (q n (r w))); last by [].
    by exists (r w).
  + apply: finite_image; exact: finite_nearest_map_finite_image hq n.
- move=> n x; exact: (set_valP (y (q n (r x)))).
- move=> n x hx.
  have he := hr.2 x hx.
  have hb := @finite_nearest_map_reference_bound R [the metricType R of metric_subset S] y q hq n (r x).
  have hy0 : y 0%N=z0 := hy.1.
  rewrite hy0 in hb.
  change (is_true (N (val (r x)-val (y (q n (r x)))) <= N (val (r x)-0))) in hb.
  by rewrite he subr0 in hb.
- move=> x hx.
  have hl := @finite_nearest_map_converges R [the metricType R of metric_subset S] y q hq hy.2 (r x).
  have hv := @metric_subset_inclusion_continuous R [the metricType R of real_norm_metric_space hN] S (r x).
  move=> U hU; apply: hl _ (hv U _).
  by rewrite (hr.2 x hx).
Qed.
