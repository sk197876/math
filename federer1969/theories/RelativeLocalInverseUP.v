(** Federer (1969), 3.4.8(10), p. 332:
    independent local inverse laws for the
    prescribed projection on Z. The
    analytic chart theorem supplies these laws;
    the finite-branch argument uses only them. *)
From mathcomp Require Import all_boot classical_sets topology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Source for [is_relative_local_inverse]:
    p_m maps Z intersect U
    homeomorphically onto a neighbourhood of
    p_m(a), 3.4.8(10), p. 332.
    Both cancellation identities and the actual
    open domains are retained. Continuity of
    the projection itself is supplied globally. *)
Definition is_relative_local_inverse (X Y:topologicalType) (P:X->Y) (Z:set X)
    (a:X) (U:set X) (V:set Y) (psi:Y->X):Prop:=
  U a /\open U /\open V /\V (P a) /\
  (forall y,V y ->Z (psi y) /\U (psi y) /\P (psi y) = y) /\
  (forall x,Z x ->U x ->psi (P x) = x) /\
  forall y,V y ->{for y,continuous psi}.
