(** Federer (1969), 2.1.5(4), pp. 56-57: inverse images of measurable sets
    under a finite regular measure. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals constructive_ereal.
From Federer Require Import MeasureUP MeasureSplit MeasurePushforward
  RegularMeasureUP RegularMeasurePartition.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [regular_measure_pushforward_measurable_preimage]:
    Federer 2.1.5(4), p. 56, with proof p. 57; under finite total
    mass and regularity, measurability for the single image measure
    suffices for inverse-image measurability. The proof applies (3)
    to the inverse images of C and its complement. *)
Theorem regular_measure_pushforward_measurable_preimage (R : realType)
    (I J : choiceType) (mu : set I -> \bar R) (hm : is_measure mu)
    (hr : is_regular_measure mu) (f : I -> J) (C : set J) :
  mu setT < +oo -> measure_measurable (measure_pushforward f mu) C ->
  measure_measurable mu (f @^-1` C).
Proof.
move=> hf hC.
have hu : (f @^-1` C) `|` (f @^-1` ~` C) = setT.
  by rewrite -preimage_setU setUCr preimage_setT.
have he : mu (f @^-1` C) + mu (f @^-1` ~` C) = mu setT.
  have h := hC setT.
  by rewrite /measure_pushforward preimage_setT setTI setTD in h.
have hU : measure_measurable mu ((f @^-1` C) `|` (f @^-1` ~` C)).
  rewrite hu; exact: measure_measurable_whole hm.
have hp := @regular_measure_additive_partition R I mu hm hr
  (f @^-1` C) (f @^-1` ~` C) hU.
rewrite hu in hp; exact: (hp he hf).1.
Qed.
