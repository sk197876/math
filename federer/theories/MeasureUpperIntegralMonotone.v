(** Federer (1969), 2.4.3(2), p. 81: monotonicity of the upper integral
    under an almost-everywhere inequality. Source context:
    PartialExtendedOrderLoci.v. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import ExtendedRealOrderTopology PartialFunctionUP MeasureUP MeasureAlmostUP MeasureAlmostBasic
  MeasureIntegralUP MeasureIntegralBounds PartialExtendedOrderLoci.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [measure_upper_function_order_transfer]: supporting inclusion
    of upper-function families in Federer 2.4.3(2), p. 81 *)
Lemma measure_upper_function_order_transfer (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu)
    (f g : partial_function X (extended_real_line R)) u :
  measure_almost_everywhere mu (partial_extended_le_locus f g) ->
  is_measure_upper_function mu g u -> is_measure_upper_function mu f u.
Proof.
move=> hfg [hu hgu]; split=> //.
apply: (@measure_almost_everywhere_mono R X mu hm _ _ _
  (@measure_almost_everywhere_and R X mu hm _ _ hfg hgu)).
move=> x [[a [b [hfa [hgb hab]]]] [y [z [huy [hgz hzy]]]]].
have ebz : b=z := partial_function_single_valued hgb hgz.
exists y,a; split=> //; split=> //.
rewrite ebz in hab; exact: le_trans hab hzy.
Qed.

(** Source for [measure_upper_integral_monotone]: direct
    monotonicity theorem Federer 2.4.3(2), p. 81.
    No measurability of f or g is imposed. *)
Theorem measure_upper_integral_monotone (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu)
    (f g : partial_function X (extended_real_line R)) :
  measure_almost_everywhere mu (partial_extended_le_locus f g) ->
  measure_upper_integral mu f <= measure_upper_integral mu g.
Proof.
move=> hfg; apply: (measure_upper_integral_specification mu g).2=> a [u [hu ha]].
apply: (@measure_upper_integral_bound R X mu f u a _ ha).
exact (@measure_upper_function_order_transfer R X mu hm f g u hfg hu).
Qed.
