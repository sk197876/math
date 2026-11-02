(** Federer (1969), 2.4.12, p. 87: finite-image density for p=infinity, with
    the finite-dimensionality hypothesis supplied by the erratum, p. 2, book
    p. 87 line 18. Our sealed nearest-candidate approximation gives such a
    finite Borel map and fixes zero by its reference-error bound. It is used
    directly on the original partial domain. its finite-dimensional norm
    comparison is recorded in FiniteNormMetricCompactness.v. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets cardinality reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric LinearBasis PartialFunctionUP PartialFunctionPostcomposition
  PartialNormedArithmetic MeasureUP MeasureAlmostUP MeasureAlmostBasic MeasurableFunctionUP MeasurablePostcomposition
  MeasureStepFunctionUP MeasurableNormedPartialRange CountablyMeasurableZeroPostcomposition
  MeasureLinfinityUP MeasureEssentialNorm MeasureEssentialNormAttainment MeasureEssentialNormComparison
  MeasureEssentialConvergence MeasureEssentialFiniteLimit CompactFiniteApproximationUP
  CompactFiniteApproximationSealed FiniteNormMetricCompactness.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [measure_linfinity_finite_image_dense]: direct corrected
    infinity-endpoint density assertion in Federer 2.4.12, p. 87; erratum p.
    2, book p. 87 line 18 A finite basis witnesses finite dimension. No
    finite measure of the source is required; zero dimension is included. *)
Theorem measure_linfinity_finite_image_dense (R : realType) (X : choiceType)
    (V : lmodType R) (N : V -> R) (hN : is_real_norm N) n (e : 'I_n -> V)
    (mu : set X -> \bar R) (hm : is_measure mu)
    (f : partial_function X (real_norm_metric_space hN)) (epsilon : R) :
  is_basis e -> is_measure_linfinity_function mu f -> (0 < epsilon)%R ->
  exists g : partial_function X (real_norm_metric_space hN),
    is_measure_linfinity_function mu g /\ finite_set (partial_function_range g) /\
    measure_essential_distance mu N f g < epsilon%:E.
Proof.
move=> he hf heps.
have hfnn := measure_essential_norm_nonnegative mu N f.
have hffin : measure_essential_norm mu N f \is a fin_num.
  rewrite (ge0_fin_numE hfnn); exact hf.2.1.
pose r := fine (measure_essential_norm mu N f).
have hfr : measure_essential_norm mu N f = r%:E by rewrite fineK.
pose delta := (epsilon/2)%R.
have hd : (0 < delta)%R by rewrite /delta divr_gt0 // ltr0n.
have hdless : (delta < epsilon)%R by rewrite /delta ltr_pdivrMr ?ltr0n // ltr_pMr // ltr1n.
pose K := [set y : real_norm_metric_space hN | (N y <= r)%R].
have hK := @finite_norm_metric_ball_compact R V N hN n e he r.
pose a := @CompactFiniteApproximation.value R (real_norm_metric_space hN) K delta 0%R hK hd.
have ha := @CompactFiniteApproximation.laws R (real_norm_metric_space hN) K delta 0%R hK hd.
pose g := partial_function_postcompose f a.
have hgmeas := @measurable_function_borel_postcomposition R X _ _ mu hm f a hf.1.1
  (compact_finite_borel ha).
have hgfinite : finite_set (partial_function_range g).
  apply: (sub_finite_set (B:= a @` setT)).
  - move=> y [x [z [hz <-]]]; by exists z.
  - exact: compact_finite_image ha.
have hgA := @measurable_normed_countable_partial_range R X V N hN mu hm g hgmeas
  (finite_set_countable hgfinite).
have ha0 : a 0%R = 0%R.
  have hb := @compact_finite_reference_error R (real_norm_metric_space hN) K delta 0%R a ha 0%R.
  change (is_true (N (0-a 0) <= N (0-0))%R) in hb.
  rewrite sub0r subrr (real_seminorm_zero hN.1) (real_seminorm_negate hN.1) in hb.
  apply: hN.2; apply/eqP; rewrite eq_le hb /=.
  exact: real_seminorm_nonnegative hN.1 _.
have hz : closed [set z : real_norm_metric_space hN | z=0%R].
  apply: accessible_closed_set1; apply: hausdorff_accessible; exact: metric_hausdorff.
have hgcount := @countably_measurable_zero_postcomposition R X
  [the topologicalType of real_norm_metric_space hN] [the topologicalType of real_norm_metric_space hN] 0%R 0%R mu hm f a
  hz ha0 (compact_finite_borel ha) hf.2.2.
have hbound := @measure_essential_norm_almost_bound R X _ mu hm N f
  (measurable_function_domain hf.1.1).
have herr : measure_essential_distance mu N f g <= delta%:E.
  apply: (@measure_essential_norm_of_almost_bound R X V mu hm N _ delta%:E).
  - rewrite lee_fin; exact: ltW hd.
  - apply: (@measure_almost_everywhere_mono R X mu hm _ _ _ hbound).
    move=> x [y [hy hny]].
    have hyK : K y by move: hny; rewrite hfr lee_fin.
    exists (y-a y)%R; split.
    + apply/partial_vector_subtract_graph; exists y,(a y); split=> //; split=> //.
      by exists y.
    + rewrite lee_fin; apply: ltW.
      exact: (@compact_finite_uniform_error R (real_norm_metric_space hN) K delta 0%R a ha y hyK).
have herrfinite : measure_essential_distance mu N f g < +oo.
  exact: le_lt_trans herr (ltry delta).
have hgfiniteNorm : measure_essential_norm mu N g < +oo.
  apply: le_lt_trans (@measure_essential_reverse_triangle_bound R X V N hN.1 mu hm f g
    (measurable_function_domain hf.1.1) (measurable_function_domain hgmeas)) _.
  exact: lte_add_pinfty hf.2.1 herrfinite.
exists g; split; first by split=> //; split.
split=> //; apply: le_lt_trans herr _; by rewrite lte_fin.
Qed.
