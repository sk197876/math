(** Federer (1969), 2.5.14, p. 108: supporting localized approximation for
    the Radon modification of 2.5.12. These lemmas separate the positive L1
    density premise from the regular-measure proof used in 2.5.9, p. 100.
    Clipping and the almost-convergent subsequence from 2.3.10, p. 80, are
    unchanged. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals
  constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric ScalarNormMetricCompleteness PartialFunctionUP
  PartialFunctionLimitUP MeasureUP MeasureAlmostUP MeasureAlmostBasic MeasurableNormedFunctionUP
  MeasureConvergenceUP FunctionLatticeUP FunctionLatticeLaws ScalarLipschitzExtensionUP
  RealIntegralFunctionalUP SummableRealFunctionUP SummableRealNormed TotalScalarLpUP
  TotalScalarLpLattice TotalScalarLpFiniteSeminorm TotalScalarPairing TotalLoneSummability
  FunctionLatticeSeminormUP FunctionSeminormDistance RegularLatticeLoneDensity
  PositiveLatticeBoundedApproximation WeightedCharacteristicExpansionUP
  PositiveVanishingWeightsSealed ExtendedRealOrderLimit RealErrorOrderLimit MeasureIntegralUP
  MeasureScalarL1Convergence MeasureConvergentSubsequence BoundedRealFunctionLowerLimit.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [dense_positive_lattice_bounded_approximation]: bounded
    version of the corrected positive-density step in Federer 2.5.9, p. 100
    The approximating function remains in L+. *)
Lemma dense_positive_lattice_bounded_approximation (R : realType) (X : choiceType)
    (L : set (X -> R)) (hL : is_function_lattice L) (F : (X -> R) -> R)
    (mu : set X -> \bar R) (hm : is_measure mu) :
  is_real_integral_functional mu L F -> is_pseudometric_dense_subset (positive_function_lattice (total_scalar_lp mu 1))
    (positive_function_lattice L) (function_seminorm_distance (finite_total_scalar_lp_norm mu 1)) ->
  forall f g e, positive_function_lattice L f ->
    positive_function_lattice (total_scalar_lp mu 1) g ->
    (forall x, (g x <= f x)%R) -> (0 < e)%R ->
    exists k, positive_function_lattice L k /\ (forall x, (k x <= f x)%R) /\
      (function_seminorm_distance (finite_total_scalar_lp_norm mu 1) g k < e)%R.
Proof.
move=> hrep hdense f g e hf hg hgf he.
have [h [hh hdist]] := hdense g hg e he.
pose k x := Order.min (h x) (f x).
have hk : positive_function_lattice L k.
  exact: (@function_lattice_minimum R X _ (@positive_function_lattice_laws R X L hL) h f hh hf).
have hhm := @represented_lattice_in_total_lone R X mu hm L F hrep h hh.1.
have hkm := @represented_lattice_in_total_lone R X mu hm L F hrep k hk.1.
have hgk := @total_scalar_lp_subtract R X mu hm 1 g k hg.1 hkm.
have hgh := @total_scalar_lp_subtract R X mu hm 1 g h hg.1 hhm.
exists k; split=> //; split.
- by move=> x; rewrite /k ge_min lexx orbT.
- apply: le_lt_trans _ hdist.
  apply: (@finite_total_scalar_lp_norm_order R X mu hm 1 _ _ hgk hgh)=> x.
  rewrite /k distrC [`|g x-h x|%R]distrC.
  exact: real_minimum_clipping_error (hgf x).
Qed.

(** Source for [dense_positive_lattice_almost_approximation]:
    supporting almost-everywhere approximation for the local uniqueness
    assertion in Federer 2.5.14, p. 108, by the argument of 2.5.9, p. 100. Every approximant
    lies in L+ and below the supplied f, including on exceptional points. *)
Theorem dense_positive_lattice_almost_approximation (R : realType) (X : choiceType)
    (L : set (X -> R)) (hL : is_function_lattice L) (F : (X -> R) -> R)
    (mu : set X -> \bar R) (hm : is_measure mu) :
  is_real_integral_functional mu L F -> is_pseudometric_dense_subset (positive_function_lattice (total_scalar_lp mu 1))
    (positive_function_lattice L) (function_seminorm_distance (finite_total_scalar_lp_norm mu 1)) ->
  forall f g, positive_function_lattice L f ->
    positive_function_lattice (total_scalar_lp mu 1) g ->
    (forall x, (g x <= f x)%R) ->
    exists k : nat -> X -> R,
      (forall n, positive_function_lattice L (k n) /\ forall x, (k n x <= f x)%R) /\
      measure_almost_everywhere mu [set x | extended_order_limit (fun n => (k n x)%:E) (g x)%:E].
Proof.
move=> hrep hdense f g hf hg hgf.
pose w := @PositiveVanishingWeights.value R.
have hw := @PositiveVanishingWeights.laws R.
have hap n := @dense_positive_lattice_bounded_approximation R X L hL F mu hm hrep hdense f g (w n)
  hf hg hgf (expansion_weights_positive hw n).
pose u n := projT1 (cid (hap n)).
have hu n := projT2 (cid (hap n)).
have hum n := @represented_lattice_in_total_lone R X mu hm L F hrep (u n) (hu n).1.1.
have hd n := @total_scalar_lp_subtract R X mu hm 1 (u n) g (hum n) hg.1.
pose e n := finite_total_scalar_lp_norm mu 1 (fun x => (u n x-g x)%R).
have he0 n : (0 <= e n)%R.
  exact: (@function_seminorm_nonnegative R X _ _ (@finite_total_scalar_lp_norm_laws R X mu hm 1) _ (hd n)).
have hew n : (e n < w n)%R.
  have hdist := (hu n).2.2.
  have hs := (function_seminorm_distance_laws
    (@total_scalar_lp_vector_lattice R X mu hm 1 (lexx _))
    (@finite_total_scalar_lp_norm_laws R X mu hm 1)).2.2.1 g (u n) hg.1 (hum n).
  by rewrite hs in hdist.
have hel : extended_order_limit (fun n => (e n)%:E) 0.
  apply: (@real_integral_error_comparison_limit R e w 0%R _ (expansion_weights_vanish hw))=> n.
  rewrite subr0 (ger0_norm (he0 n)); exact: ltW (hew n).
have hei n : is_measure_integral mu (real_total_integrand (fun x => `|u n x-g x|%R)) (e n)%:E.
  exact: (@total_scalar_lone_absolute_integral R X mu hm _ (hd n)).
have hconv := @real_total_l1_converges_in_measure R X mu hm u g e hei hel.
have hUn n : @is_measurable_normed_function R X R^o (fun x : R => `|x|%R)
    (scalar_absolute_value_norm R) mu (total_scalar_function (u n)).
  apply: (@summable_real_function_in_normed_collection R X mu hm (u n)).
  exists (F (u n)); exact: hrep _ (hu n).1.1.
have hgn := @summable_real_function_in_normed_collection R X mu hm g
  (@total_lone_summable_real R X mu hm g hg.1).
have [s [hs hsa]] := @convergent_in_measure_almost_subsequence R X R^o
  (fun x : R => `|x|%R) (scalar_absolute_value_norm R) (@scalar_norm_metric_complete R)
  mu hm (fun n => total_scalar_function (u n)) (total_scalar_function g) hUn hgn hconv.
exists (fun n => u (s n)); split.
- move=> n; split; [exact: (hu (s n)).1|exact: (hu (s n)).2.1].
- apply: (@measure_almost_everywhere_mono R X mu hm _ _ _ hsa)=> x hx.
  exact: (@total_scalar_limit_locus_order_limit R X (fun n => u (s n)) g x hx).
Qed.
