(** Federer (1969), 2.4.15, p. 89: necessity of the global norm proportions
    when both input norms are positive. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric PartialFunctionUP PartialNormedArithmetic
  RealPower ConjugateExponents NormPowerScalar MinkowskiEqualityUP MinkowskiNormalisedProportions
  MeasureConjugateNormPower MeasureHolderNormEquality MinkowskiIntegralSaturation MeasureLpNorm
  MeasureUP MeasurableNormedFunctionUP MeasurableNormedArithmetic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [minkowski_positive_norm_equality_necessary]:
    positive-norm necessity in the general equality criterion
    of Federer 2.4.15, p. 89. The coefficients
    are the input norms divided by their sum, hence are
    nonnegative and sum to one. No pointwise choice of
    coefficients is made. *)
Lemma minkowski_positive_norm_equality_necessary (R : realType) (X : choiceType)
    (V : lmodType R) (N : V -> R) (hN : is_real_norm N)
    (mu : set X -> \bar R) (hm : is_measure mu) (p a b : R)
    (f g : partial_function X (real_norm_metric_space hN)) :
  (1 < p)%R -> (0 < a)%R -> (0 < b)%R ->
  is_measurable_normed_function mu f -> is_measurable_normed_function mu g ->
  measure_lp_norm mu N p f = a%:E -> measure_lp_norm mu N p g = b%:E ->
  measure_lp_norm mu N p (partial_vector_add f g) = (a+b)%:E ->
  is_minkowski_equality_condition N mu f g.
Proof.
move=> hp ha hb hf hg hfa hgb hsc.
pose c := (a+b)%R; have hc : (0 < c)%R := addr_gt0 ha hb.
pose q := finite_conjugate_exponent p.
have hq : (1 < q)%R := @finite_conjugate_exponent_strict R p hp.
have hpq := @finite_conjugate_exponent_reciprocals R p hp.
have hr : (0 < p-1)%R by rewrite subr_gt0.
have hrq := @finite_conjugate_exponent_product R p hp.
have hp0 : (0 < p)%R := lt_trans (ltr01) hp.
have hq0 : (0 < q)%R := lt_trans (ltr01) hq.
have hsum := @measurable_normed_function_add R X V N hN mu hm f g hf hg.
pose w := partial_scalar_norm_power N (p-1)%R (partial_vector_add f g).
have [hw hwn] := @measure_conjugate_norm_power R X V N hN mu hm p q (p-1)%R c
  (partial_vector_add f g) (ltW hp) (ltW hq) hr hrq hsum.1 hsc.
have hd := @real_power_strictly_positive R c (p-1)%R hc.
have [hfi hgi] := @minkowski_equality_holder_integrals R X V N hN mu hm p a b c f g
  hp hf hg hfa hgb hsc erefl.
have hef := @holder_norm_product_positive_equality R X V R^o N (fun t : R => `|t|%R)
  hN (scalar_absolute_value_norm R) mu hm p q a (real_power c (p-1)%R) f w
  (ltW hp) (ltW hq) hpq ha hd hf.1 hw hfa hwn hfi.
have heg := @holder_norm_product_positive_equality R X V R^o N (fun t : R => `|t|%R)
  hN (scalar_absolute_value_norm R) mu hm p q b (real_power c (p-1)%R) g w
  (ltW hp) (ltW hq) hpq hb hd hg.1 hw hgb hwn hgi.
have hprop := @minkowski_two_normalised_proportions R X V N hN mu hm p q (p-1)%R a b c f g
  hp0 hq0 hr hrq ha hb hc hef heg.
exists (a/c)%R,(b/c)%R; split; first exact: divr_ge0 (ltW ha) (ltW hc).
split; first exact: divr_ge0 (ltW hb) (ltW hc).
split=> //; by rewrite -mulrDl /c divff ?gt_eqF.
Qed.
