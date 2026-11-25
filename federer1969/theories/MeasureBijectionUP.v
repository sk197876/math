(** Federer (1969), 2.6.5, pp. 119–120: products are identified by the
    displayed coordinate bijections. This abstract predicate specifies a
    bijection, its inverse, and its image-measure law. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal.
From Federer Require Import MeasurePushforward.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [is_measure_bijection]: supporting abstract
    laws for the coordinate identifications of Federer
    2.6.5, pp. 119–120. Inverse maps are explicit,
    so no choice of an inverse is hidden in downstream proofs. *)
Record is_measure_bijection (R : realType) (X Y : choiceType)
    (mu : set X -> \bar R) (nu : set Y -> \bar R) (f : X -> Y) (g : Y -> X) : Prop := {
  (** Source for [measure_bijection_cancel]: first inverse
      identity for Federer 2.6.5, pp. 119–120. *)
  measure_bijection_cancel : cancel f g;
  (** Source for [measure_bijection_inverse_cancel]: second
      inverse identity for Federer 2.6.5, pp. 119–120. *)
  measure_bijection_inverse_cancel : cancel g f;
  (** Source for [measure_bijection_pushforward]: image-measure
      identity of Federer 2.6.5, pp. 119–120. *)
  measure_bijection_pushforward : measure_pushforward f mu = nu
}.
