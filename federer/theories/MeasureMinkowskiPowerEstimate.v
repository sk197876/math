(** Federer (1969), 2.4.15, final proof display p. 89: the two Holder
    applications bound the p-th power of the sum norm. The second factor in
    each application is |f+g|^(p-1), correcting the scan-verified missing
    exponent. The norm of f+g is finite at this stage, as proved separately
    before the Holder applications. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric ExtendedRealPartial PartialFunctionUP PartialNormedArithmetic
  PartialNormPower PartialNormProduct PartialExtendedArithmetic PartialExtendedOrderLoci DominatedErrorGraphs
  RealPower NormPowerScalar MinkowskiScalarBound ConjugateExponents
  MeasureConjugateNormPower MeasureLpPowerIntegral MeasureLpNorm MeasureHolderNormProduct
  MeasureUP MeasureAlmostUP MeasureAlmostBasic MeasurableFunctionUP MeasurableNormedFunctionUP MeasurableNormedArithmetic
  MeasureIntegralUP MeasureIntegralAddition MeasureIntegralComparison.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [measure_minkowski_holder_integrals]: the last integral
    estimates in Federer 2.4.15, p. 89 It is proved by two instances of the
    project's norm-product Holder theorem. The two integral values and their
    separate bounds are exposed for the later equality proof. No division by
    the sum norm occurs here. *)
Lemma measure_minkowski_holder_integrals (R : realType) (X : choiceType)
    (V : lmodType R) (N : V -> R) (hN : is_real_norm N)
    (mu : set X -> \bar R) (hm : is_measure mu) (p a b c : R)
    (f g : partial_function X (real_norm_metric_space hN)) :
  (1 < p)%R -> is_measurable_normed_function mu f -> is_measurable_normed_function mu g ->
  measure_lp_norm mu N p f = a%:E -> measure_lp_norm mu N p g = b%:E ->
  measure_lp_norm mu N p (partial_vector_add f g) = c%:E ->
  exists u v : R,
    is_measure_integral mu (partial_norm_product N (fun t : R => `|t|%R) f
      (partial_scalar_norm_power N (p-1)%R (partial_vector_add f g))) u%:E /\
    is_measure_integral mu (partial_norm_product N (fun t : R => `|t|%R) g
      (partial_scalar_norm_power N (p-1)%R (partial_vector_add f g))) v%:E /\
    (u <= a*real_power c (p-1))%R /\ (v <= b*real_power c (p-1))%R /\
    (real_power c p <= u+v)%R.
Proof.
move=> hp hf hg hfa hgb hsc.
pose q := finite_conjugate_exponent p.
have hq : (1 < q)%R := @finite_conjugate_exponent_strict R p hp.
have hpq := @finite_conjugate_exponent_reciprocals R p hp.
have hr : (0 < p-1)%R by rewrite subr_gt0.
have hrq := @finite_conjugate_exponent_product R p hp.
have hsum := @measurable_normed_function_add R X V N hN mu hm f g hf hg.
pose w := partial_scalar_norm_power N (p-1)%R (partial_vector_add f g).
have [hw hwn] := @measure_conjugate_norm_power R X V N hN mu hm p q (p-1)%R c
  (partial_vector_add f g) (ltW hp) (ltW hq) hr hrq hsum.1 hsc.
have [u [hu0 [hui hub]]] := @measure_holder_finite_norms R X V R^o N (fun t : R => `|t|%R)
  hN (scalar_absolute_value_norm R) mu hm p q a (real_power c (p-1)%R) f w
  (ltW hp) (ltW hq) hpq hf.1 hw hfa hwn.
have [v [hv0 [hvi hvb]]] := @measure_holder_finite_norms R X V R^o N (fun t : R => `|t|%R)
  hN (scalar_absolute_value_norm R) mu hm p q b (real_power c (p-1)%R) g w
  (ltW hp) (ltW hq) hpq hg.1 hw hgb hwn.
have hadd : extended_add u%:E v%:E = Some (u+v)%:E by rewrite /extended_add /=.
have hright := @measure_integral_add R X mu hm _ _ _ _ _ hui hvi hadd.
have hleft := @measure_power_integral_from_finite_lp_norm R X V N hN mu hm p c
  (partial_vector_add f g) (ltW hp) hsum.1 hsc.
have hord : measure_almost_everywhere mu (partial_extended_le_locus
    (partial_norm_power N p (partial_vector_add f g))
    (partial_extended_function_add (partial_norm_product N (fun t : R => `|t|%R) f w)
      (partial_norm_product N (fun t : R => `|t|%R) g w))).
  apply: (@measure_almost_everywhere_mono R X mu hm _ _ _
    (@measure_almost_everywhere_and R X mu hm _ _ (measurable_function_domain hf.1) (measurable_function_domain hg.1))).
  move=> x [[s hs] [t ht]].
  have hst : partial_function_graph (partial_vector_add f g) x (s+t)%R.
    apply/partial_vector_add_graph; exists s,t; by split=> //; split.
  have hweight : partial_function_graph w x (real_power (N (s+t)%R) (p-1)%R).
    exists (s+t)%R; by split.
  pose d := real_power (N (s+t)%R) (p-1)%R.
  have hd0 : (0 <= d)%R := real_power_nonnegative _ _.
  have hfw : partial_function_graph (partial_norm_product N (fun t : R => `|t|%R) f w) x (N s*d)%:E.
    apply/(@partial_norm_product_graph R X V R^o N _ hN (scalar_absolute_value_norm R)).
    exists s,d; split=> //; split=> //; by rewrite (ger0_norm hd0).
  have hgw : partial_function_graph (partial_norm_product N (fun t : R => `|t|%R) g w) x (N t*d)%:E.
    apply/(@partial_norm_product_graph R X V R^o N _ hN (scalar_absolute_value_norm R)).
    exists t,d; split=> //; split=> //; by rewrite (ger0_norm hd0).
  exists (real_power (N (s+t)%R) p)%:E,(N s*d+N t*d)%:E; split.
  - exists (s+t)%R; by split.
  - split; first exact (@partial_finite_sum_graph R X _ _ x _ _ hfw hgw).
    rewrite lee_fin; exact (@norm_sum_holder_factor_bound R V N hN p s t hp).
have hbnd := @measure_integral_monotone R X mu hm _ _ _ _ hleft hright hord.
rewrite lee_fin in hbnd.
exists u,v; split=> //; split=> //; split=> //; split=> //.
Qed.

(** Source for [measure_minkowski_power_estimate]: the last integral
    estimate in Federer 2.4.15, p. 89 It is proved by two instances of the
    project's norm-product Holder theorem. No division by the sum norm
    occurs here. *)
Lemma measure_minkowski_power_estimate (R : realType) (X : choiceType)
    (V : lmodType R) (N : V -> R) (hN : is_real_norm N)
    (mu : set X -> \bar R) (hm : is_measure mu) (p a b c : R)
    (f g : partial_function X (real_norm_metric_space hN)) :
  (1 < p)%R -> is_measurable_normed_function mu f -> is_measurable_normed_function mu g ->
  measure_lp_norm mu N p f = a%:E -> measure_lp_norm mu N p g = b%:E ->
  measure_lp_norm mu N p (partial_vector_add f g) = c%:E ->
  (real_power c p <= (a+b)*real_power c (p-1))%R.
Proof.
move=> hp hf hg hfa hgb hsc.
have [u [v [hui [hvi [hub [hvb hbnd]]]]]] :=
  @measure_minkowski_holder_integrals R X V N hN mu hm p a b c f g hp hf hg hfa hgb hsc.
apply: le_trans hbnd _.
rewrite mulrDl; exact: lerD hub hvb.
Qed.
