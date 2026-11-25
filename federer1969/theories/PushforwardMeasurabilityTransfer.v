(** Federer (1969), 2.1.2, p. 54, and 2.4.18, pp. 90-91: measurability for
    an image measure u_#(mu) under an injective map transfers to inverse
    images. The strips of Federer 2.5.11, p. 102, are images of the factor
    spaces under injective coordinate maps; the sections of a measurable
    function are then measurable for the factor measures. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import PartialFunctionUP PartialFunctionPrecomposition MeasureUP
  MeasurePushforward MeasureAlmostUP MeasurableFunctionUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [measure_pushforward_preimage_measurable]: supporting
    converse to the last sentence of Federer 2.1.2, p. 54, for an
    injective map: a set measurable for u_#(mu) has mu measurable
    inverse image. Test sets are transported to their images. *)
Lemma measure_pushforward_preimage_measurable (R : realType) (X Y : choiceType)
    (u : X -> Y) (mu : set X -> \bar R) (M : set Y) :
  injective u -> measure_measurable (measure_pushforward u mu) M ->
  measure_measurable mu (u @^-1` M).
Proof.
move=> hu hM T.
have hpre : u @^-1` (u @` T) = T.
  apply/seteqP; split=> [x [y hy hxy]|x hx]; last by exists x.
  by rewrite -(hu _ _ hxy).
have := hM (u @` T).
by rewrite /measure_pushforward preimage_setI setDE preimage_setI -preimage_setC -setDE hpre.
Qed.

(** Source for [measurable_function_pushforward_precompose]: supporting
    measurability of f composed with u for mu, when f is measurable for
    u_#(mu) and u is injective; compare Federer 2.4.18, p. 90, where
    this composition is integrated. *)
Lemma measurable_function_pushforward_precompose (R : realType) (X Y : choiceType)
    (Z : topologicalType) (u : X -> Y) (mu : set X -> \bar R)
    (f : partial_function Y Z) :
  injective u -> is_measure_measurable_function (measure_pushforward u mu) f ->
  is_measure_measurable_function mu (partial_function_precompose u f).
Proof.
move=> hu [hdom hopen]; split.
- rewrite /measure_almost_everywhere partial_function_precompose_domain preimage_setC.
  exact: hdom.
- move=> U hU; rewrite partial_function_precompose_preimage.
  exact: measure_pushforward_preimage_measurable hu (hopen U hU).
Qed.
