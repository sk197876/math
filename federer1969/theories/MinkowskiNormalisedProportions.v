(** Federer (1969), 2.4.15, p. 89: the global norm proportions obtained from
    the two Holder equalities. These supporting graph calculations use one
    common conull set. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric PartialFunctionUP PartialNormedArithmetic PartialNormPower
  RealPower NormPowerScalar NormalisedNormPowerValues MinkowskiPowerProportion MinkowskiEqualityUP
  MeasureUP MeasureAlmostUP MeasureAlmostBasic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [minkowski_two_normalised_proportions]: supporting
    derivation of both printed pointwise norm identities in
    Federer 2.4.15, p. 89. The positive
    denominators a,b,c are the three norm values; the
    coefficients a/c and b/c are independent of the point. *)
Lemma minkowski_two_normalised_proportions (R : realType) (X : choiceType)
    (V : lmodType R) (N : V -> R) (hN : is_real_norm N)
    (mu : set X -> \bar R) (hm : is_measure mu) (p q r a b c : R)
    (f g : partial_function X (real_norm_metric_space hN)) :
  0 < p -> 0 < q -> 0 < r -> r*q=p -> 0 < a -> 0 < b -> 0 < c ->
  measure_almost_equal mu (partial_norm_power N p (partial_vector_scale a^-1 f))
    (partial_norm_power (fun t : R => `|t|) q
      (partial_vector_scale (real_power c r)^-1 (partial_scalar_norm_power N r (partial_vector_add f g)))) ->
  measure_almost_equal mu (partial_norm_power N p (partial_vector_scale b^-1 g))
    (partial_norm_power (fun t : R => `|t|) q
      (partial_vector_scale (real_power c r)^-1 (partial_scalar_norm_power N r (partial_vector_add f g)))) ->
  measure_almost_everywhere mu (minkowski_norm_proportion_locus N (a/c) (b/c) f g).
Proof.
move=> hp hq hr hrq ha hb hc hfe hge.
have hd := @real_power_strictly_positive R c r hc.
have hef := @normalised_norm_power_equal_values R X V R^o N _ hN (scalar_absolute_value_norm R)
  mu hm p q a (real_power c r) f _ ha hd hfe.
have heg := @normalised_norm_power_equal_values R X V R^o N _ hN (scalar_absolute_value_norm R)
  mu hm p q b (real_power c r) g _ hb hd hge.
apply: (@measure_almost_everywhere_mono R X mu hm _ _ _
  (@measure_almost_everywhere_and R X mu hm _ _ hef heg)).
move=> x [[u [z [hu [hz heF]]]] [v [w [hv [hw heG]]]]].
have hzw : z=w := partial_function_single_valued hz hw.
rewrite -hzw in heG.
have [s [hs hsz]] := hz.
have [u0 [v0 [hu0 [hv0 hsadd]]]] := (partial_vector_add_graph f g x s).1 hs.
have heu : u0=u := partial_function_single_valued hu0 hu.
have hev : v0=v := partial_function_single_valued hv0 hv.
have hzval : z=real_power (N (u+v)) r by rewrite -hsz hsadd heu hev.
rewrite hzval (ger0_norm (real_power_nonnegative _ _)) in heF.
rewrite hzval (ger0_norm (real_power_nonnegative _ _)) in heG.
exists u,v; split=> //; split=> //; split.
- exact (@minkowski_normalised_power_proportion R p q r a c (N u) (N (u+v)) hp hq hr hrq ha hc
    (real_seminorm_nonnegative hN.1 u) (real_seminorm_nonnegative hN.1 _) heF).
- exact (@minkowski_normalised_power_proportion R p q r b c (N v) (N (u+v)) hp hq hr hrq hb hc
    (real_seminorm_nonnegative hN.1 v) (real_seminorm_nonnegative hN.1 _) heG).
Qed.
