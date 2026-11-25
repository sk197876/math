(** Federer (1969), 2.4.14, p. 88: the final equality inference from equal
    normalised powers and a fixed product sign. These supporting lemmas
    combine the two conull sets before using scalar sign algebra. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric ExtendedRealOrderTopology PartialFunctionUP PartialNormPower
  RealPower SignedRealPower SignedPowerEquality PartialSignedPower PartialScalarProduct
  PartialExtendedOrderLoci MeasureIntegralNegation MeasureUP MeasureAlmostUP MeasureAlmostBasic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [equal_powers_positive_product_almost_signed]: positive-sign
    conclusion in the equality proof of Federer 2.4.14, p. 88 The global
    proportionality coefficient is one for these normalised signed powers. *)
Lemma equal_powers_positive_product_almost_signed (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu) (p q : R)
    (f g : partial_function X (real_norm_metric_space (scalar_absolute_value_norm R))) :
  (0 < p)%R -> (0 < q)%R ->
  measure_almost_equal mu (partial_norm_power (fun a : R => `|a|%R) p f)
    (partial_norm_power (fun a : R => `|a|%R) q g) ->
  measure_almost_everywhere mu (partial_extended_nonnegative_locus (partial_scalar_product f g)) ->
  measure_almost_everywhere mu (partial_signed_power_dependence_locus p q 1%R f g).
Proof.
move=> hp hq he hsign.
apply: (@measure_almost_everywhere_mono R X mu hm _ _ _
  (@measure_almost_everywhere_and R X mu hm _ _ he hsign)).
move=> x [[z [[a [ha haz]] [b [hb hbz]]]] [w [hw hw0]]].
have heE : (real_power `|a|%R p)%:E = (real_power `|b|%R q)%:E by rewrite haz hbz.
have hpow := EFin_inj heE.
have hpgraph : partial_function_graph (partial_scalar_product f g) x (a*b)%:E.
  apply/partial_scalar_product_graph; exists a,b; by split=> //; split.
have hvalue := partial_function_single_valued hpgraph hw.
have hab : (0 <= a*b)%R by move: hw0; rewrite -hvalue lee_fin.
exists a,b; split=> //; split=> //; rewrite mul1r.
exact (@equal_powers_nonnegative_product_signed R p q a b hp hq hpow hab).
Qed.

(** Source for [equal_powers_negative_product_almost_signed]: negative-sign
    conclusion in the equality proof of Federer 2.4.14, p. 88 The global
    proportionality coefficient is minus one. *)
Lemma equal_powers_negative_product_almost_signed (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu) (p q : R)
    (f g : partial_function X (real_norm_metric_space (scalar_absolute_value_norm R))) :
  (0 < p)%R -> (0 < q)%R ->
  measure_almost_equal mu (partial_norm_power (fun a : R => `|a|%R) p f)
    (partial_norm_power (fun a : R => `|a|%R) q g) ->
  measure_almost_everywhere mu (partial_extended_nonnegative_locus
    (partial_extended_function_negate (partial_scalar_product f g))) ->
  measure_almost_everywhere mu (partial_signed_power_dependence_locus p q (-1)%R f g).
Proof.
move=> hp hq he hsign.
apply: (@measure_almost_everywhere_mono R X mu hm _ _ _
  (@measure_almost_everywhere_and R X mu hm _ _ he hsign)).
move=> x [[z [[a [ha haz]] [b [hb hbz]]]] [w [[v [hv hvw]] hw0]]].
have heE : (real_power `|a|%R p)%:E = (real_power `|b|%R q)%:E by rewrite haz hbz.
have hpow := EFin_inj heE.
have hpgraph : partial_function_graph (partial_scalar_product f g) x (a*b)%:E.
  apply/partial_scalar_product_graph; exists a,b; by split=> //; split.
have hvalue := partial_function_single_valued hpgraph hv.
have hab : (a*b <= 0)%R by move: hw0; rewrite -hvw -hvalue lee_fin oppr_ge0.
exists a,b; split=> //; split=> //; rewrite mulN1r.
exact (@equal_powers_nonpositive_product_signed R p q a b hp hq hpow hab).
Qed.
