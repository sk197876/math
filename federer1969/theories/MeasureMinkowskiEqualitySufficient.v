(** Federer (1969), 2.4.15, p. 89: sufficiency of the norm-proportion
    equality condition. The proof uses norm equality almost everywhere,
    homogeneity and the sum of the global coefficients; it applies also to
    p=1. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric PartialFunctionUP PartialNormedArithmetic
  MinkowskiEqualityUP MeasureLpNormAlmostEquality MeasureLpNormScale NormPowerScale
  MeasureLpNorm MeasureLpMembershipUP MeasureLpSumMembership
  MeasureUP MeasureAlmostUP MeasureAlmostBasic MeasurableFunctionUP MeasurableNormedArithmetic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [minkowski_equality_condition_sufficient]: the sufficiency
    direction of the general equality condition in Federer 2.4.15, p. 89 The
    target is any normed space, and the stronger finite-p statement includes
    p=1. *)
Theorem minkowski_equality_condition_sufficient (R : realType) (X : choiceType)
    (V : lmodType R) (N : V -> R) (hN : is_real_norm N)
    (mu : set X -> \bar R) (hm : is_measure mu) (p : R)
    (f g : partial_function X (real_norm_metric_space hN)) :
  is_measure_lp_function mu p f -> is_measure_lp_function mu p g ->
  is_minkowski_equality_condition N mu f g ->
  measure_lp_norm mu N p (partial_vector_add f g) = measure_lp_norm mu N p f + measure_lp_norm mu N p g.
Proof.
move=> hf hg [a [b [ha [hb [hab he]]]]].
have hs := @measure_lp_function_add R X V N hN mu hm p f g hf hg.
have hsa := @measurable_normed_scalar_multiple R X V N hN mu hm a (partial_vector_add f g) hs.2.1.1.
have hsb := @measurable_normed_scalar_multiple R X V N hN mu hm b (partial_vector_add f g) hs.2.1.1.
have hea : measure_almost_everywhere mu (partial_norm_equality_locus N f (partial_vector_scale a (partial_vector_add f g))).
  apply: (@measure_almost_everywhere_mono R X mu hm _ _ _ he).
  move=> x [u [v [hu [hv [hnu hnv]]]]]; exists u,(a *: (u+v))%R; split=> //; split.
  - exists (u+v)%R; split=> //; apply/partial_vector_add_graph; exists u,v; by split=> //; split.
  - by rewrite (real_seminorm_scale hN.1) (ger0_norm ha).
have heb : measure_almost_everywhere mu (partial_norm_equality_locus N g (partial_vector_scale b (partial_vector_add f g))).
  apply: (@measure_almost_everywhere_mono R X mu hm _ _ _ he).
  move=> x [u [v [hu [hv [hnu hnv]]]]]; exists v,(b *: (u+v))%R; split=> //; split.
  - exists (u+v)%R; split=> //; apply/partial_vector_add_graph; exists u,v; by split=> //; split.
  - by rewrite (real_seminorm_scale hN.1) (ger0_norm hb).
have hfa := @measure_lp_norm_almost_norm_equal R X V N hN mu hm p f _ hf.1 hf.2.1.1 hsa hea.
have hgb := @measure_lp_norm_almost_norm_equal R X V N hN mu hm p g _ hg.1 hg.2.1.1 hsb heb.
rewrite (@measure_lp_norm_scale R X V N hN mu hm p a _ hf.1 hs.2.1.1) (ger0_norm ha) in hfa.
rewrite (@measure_lp_norm_scale R X V N hN mu hm p b _ hg.1 hs.2.1.1) (ger0_norm hb) in hgb.
have hsnn := @measure_lp_norm_nonnegative R X V N hN mu p _ hm hs.1 hs.2.1.1.
have hsfin : measure_lp_norm mu N p (partial_vector_add f g) \is a fin_num.
  rewrite (ge0_fin_numE hsnn); exact hs.2.2.1.
rewrite hfa hgb -(fineK hsfin) -!EFinM -EFinD -mulrDl hab mul1r.
reflexivity.
Qed.
