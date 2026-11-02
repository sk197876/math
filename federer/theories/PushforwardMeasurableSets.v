(** Federer (1969), 2.2.17, p. 72, image measure laws left as exercises: a
    target set is measurable if its inverse image is measurable. This is the
    direct implication of 2.1.2, p. 54 Source context: ProperMapUP.v. *)
From mathcomp Require Import all_boot all_algebra classical_sets reals constructive_ereal.
From Federer Require Import MeasureUP MeasurePushforward.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [pushforward_measurable_from_preimage]: supporting
    measurable-set law for Federer 2.2.17, p. 72,
    obtained by splitting each inverse-image test set. The
    map need not be continuous or proper for this implication. *)
Lemma pushforward_measurable_from_preimage (R : realType) (X Y : choiceType)
    (mu : set X -> \bar R) (f : X -> Y) (B : set Y) :
  measure_measurable mu (f @^-1` B) -> measure_measurable (measure_pushforward f mu) B.
Proof.
move=> h T; rewrite /measure_pushforward preimage_setI !setDE preimage_setI preimage_setC.
by rewrite -setDE; exact: h.
Qed.
