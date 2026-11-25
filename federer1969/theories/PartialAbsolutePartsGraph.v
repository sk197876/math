(** Federer (1969), final paragraph of the proof of 2.4.4, p. 83: |f|=f++f-
    pointwise, including infinite values. This graph identity supplies the
    corresponding integral formula. Source context:
    MeasureIntegralSqueeze.v. *)
From mathcomp Require Import all_boot all_order all_algebra reals constructive_ereal topology.
From Federer Require Import ExtendedRealPartial ExtendedRealOrderTopology PartialFunctionUP PartialFunctionPostcomposition
  PartialExtendedArithmetic PartialFunctionIntegralParts MeasureUpperIntegralPositivePart.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ereal_scope.

(** Source for [partial_extended_function_absolute_value]: the
    absolute value in Federer 2.4.4(7)–(8), p. 82,
    retaining f's exact domain. *)
Definition partial_extended_function_absolute_value (R : realType) (X : Type)
    (f : partial_function X (extended_real_line R)) :=
  partial_function_postcompose f (fun y => (`|y| : extended_real_line R)).

(** Source for [partial_absolute_parts_graph]: the pointwise
    identity used in the final proof paragraph of Federer
    2.4.4, p. 83. Both parts are nonnegative, so their
    sum is defined even when the absolute value is infinite. *)
Lemma partial_absolute_parts_graph (R : realType) (X : Type)
    (f : partial_function X (extended_real_line R)) x y :
  partial_function_graph (partial_extended_function_add (partial_extended_function_positive_part f)
    (partial_extended_function_negative_part f)) x y <->
  partial_function_graph (partial_extended_function_absolute_value f) x y.
Proof.
split.
- move=> h; have [p [n [[a [ha hap]] [[b [hb hbn]] hpn]]]] :=
    (@partial_extended_function_add_graph R X _ _ x y).1 h.
  have hab := partial_function_single_valued ha hb.
  rewrite -hab in hbn; rewrite -hap -hbn in hpn.
  have hd := ge0_adde_def (extended_positive_part_nonnegative a) (extended_negative_part_nonnegative a).
  rewrite /extended_add hd -extended_absolute_parts in hpn.
  case: hpn=> he; exists a; by split.
- move=> [a [ha hay]]; apply/partial_extended_function_add_graph.
  exists (extended_positive_part a),(extended_negative_part a); split.
  + exists a; by split.
  split; first by exists a; split.
  have hd := ge0_adde_def (extended_positive_part_nonnegative a) (extended_negative_part_nonnegative a).
  by rewrite /extended_add hd -extended_absolute_parts hay.
Qed.
