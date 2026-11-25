(** Federer (1969), 2.4.2, p. 81: the upper integral is positive infinity
    when no upper function exists, and the lower integral is negative
    infinity when no lower function exists. Source context:
    MeasureIntegralUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import ExtendedRealOrderTopology PartialFunctionUP MeasureIntegralUP MeasureIntegralBounds.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [measure_upper_integral_no_upper_function]: direct
    empty-family convention in Federer 2.4.2, p. 81. *)
Theorem measure_upper_integral_no_upper_function (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (f : partial_function X (extended_real_line R)) :
  (~ exists u, is_measure_upper_function mu f u) -> measure_upper_integral mu f = +oo.
Proof.
move=> hn; apply/eqP; rewrite eq_le leey /=.
apply: (measure_upper_integral_specification mu f).2=> b [u [hu _]].
exfalso; apply: hn; by exists u.
Qed.

(** Source for [measure_lower_integral_no_lower_function]: direct
    dual empty-family convention in Federer 2.4.2, p. 81. *)
Theorem measure_lower_integral_no_lower_function (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (f : partial_function X (extended_real_line R)) :
  (~ exists u, is_measure_lower_function mu f u) -> measure_lower_integral mu f = -oo.
Proof.
move=> hn; apply/eqP; rewrite eq_le leNye andbT.
apply: (measure_lower_integral_specification mu f).2=> b [u [hu _]].
exfalso; apply: hn; by exists u.
Qed.
