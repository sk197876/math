(** Federer (1969), 3.1.1, p. 209: the polarity into the continuous
    real dual, specified independently of a carrier or representation. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import Hom.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Source for [is_continuous_polarity]: the polarity in the second
    special case of Federer 3.1.1, p. 209. Under the dual evaluation,
    the image of u is the functional v mapped to the inner product v.u. *)
Definition is_continuous_polarity (R : realType) (V D : lmodType R)
    (B : V -> V -> R) (evaluation : Hom D (Hom V R^o)) (P : Hom V D) :=
  forall u v, evaluation (P u) v = B v u.
