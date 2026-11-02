(** Federer (1969), 2.4.14, p. 88: the converse equality argument for
    normalised signed powers. These supporting lemmas recover equal powers
    and a fixed product sign on conull sets. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric ExtendedRealOrderTopology PartialFunctionUP PartialNormPower
  RealPower SignedRealPower SignedPowerConverse PartialSignedPower PartialScalarProduct
  PartialExtendedOrderLoci MeasureIntegralNegation MeasureUP MeasureAlmostUP MeasureAlmostBasic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [almost_equal_signed_powers_absolute_and_sign]: converse
    positive-sign conditions in Federer 2.4.14, p. 88 The coefficient one
    identifies the normalised signed powers. *)
Lemma almost_equal_signed_powers_absolute_and_sign (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu) (p q : R)
    (f g : partial_function X (real_norm_metric_space (scalar_absolute_value_norm R))) :
  (0 < p)%R -> (0 < q)%R ->
  measure_almost_everywhere mu (partial_signed_power_dependence_locus p q 1%R f g) ->
  measure_almost_equal mu (partial_norm_power (fun a : R => `|a|%R) p f)
    (partial_norm_power (fun a : R => `|a|%R) q g) /\
  measure_almost_everywhere mu (partial_extended_nonnegative_locus (partial_scalar_product f g)).
Proof.
move=> hp hq he; split;
  apply: (@measure_almost_everywhere_mono R X mu hm _ _ _ he);
  move=> x [a [b [ha [hb hab]]]]; rewrite mul1r in hab;
  have [hpow hsign] := @signed_power_equality_absolute_and_sign R p q a b hp hq hab.
- exists (real_power `|a|%R p)%:E; split; first by exists a; split.
  exists b; split=> //; by rewrite hpow.
- exists (a*b)%:E; split; last by rewrite lee_fin.
  apply/partial_scalar_product_graph; exists a,b; by split=> //; split.
Qed.

(** Source for [almost_opposite_signed_powers_absolute_and_sign]: converse
    negative-sign conditions in Federer 2.4.14, p. 88 The coefficient minus
    one gives the opposite normalised powers. *)
Lemma almost_opposite_signed_powers_absolute_and_sign (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu) (p q : R)
    (f g : partial_function X (real_norm_metric_space (scalar_absolute_value_norm R))) :
  (0 < p)%R -> (0 < q)%R ->
  measure_almost_everywhere mu (partial_signed_power_dependence_locus p q (-1)%R f g) ->
  measure_almost_equal mu (partial_norm_power (fun a : R => `|a|%R) p f)
    (partial_norm_power (fun a : R => `|a|%R) q g) /\
  measure_almost_everywhere mu (partial_extended_nonnegative_locus
    (partial_extended_function_negate (partial_scalar_product f g))).
Proof.
move=> hp hq he; split;
  apply: (@measure_almost_everywhere_mono R X mu hm _ _ _ he);
  move=> x [a [b [ha [hb hab]]]]; rewrite mulN1r in hab;
  have [hpow hsign] := @signed_power_opposite_absolute_and_sign R p q a b hp hq hab.
- exists (real_power `|a|%R p)%:E; split; first by exists a; split.
  exists b; split=> //; by rewrite hpow.
- exists (-(a*b))%:E; split; last by rewrite lee_fin oppr_ge0.
  exists (a*b)%:E; split=> //.
  apply/partial_scalar_product_graph; exists a,b; by split=> //; split.
Qed.
