(** Elementary set identities supporting the coordinate-line tests in
    Federer (1969), 2.5.10, p. 101. These identify a subset of a
    parametrised segment with the image of its scalar parameter trace; they
    are set-theoretic infrastructure, not new book claims. *)
From mathcomp Require Import all_boot classical_sets.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [image_intersection_trace]: supporting
    set identity for the horizontal and vertical threshold
    tests of Federer 2.5.10, p. 101.
    Injectivity is unnecessary for this identity. *)
Lemma image_intersection_trace (X Y : Type) (f : X -> Y) (I : set X) (B : set Y) :
  (f @` I) `&` B=f @` (I `&` (f @^-1` B)).
Proof.
apply/seteqP; split.
- move=> y [[x hx <-] hy]; exists x=> //; by split.
- move=> y [x [hx hy] <-]; split=> //; by exists x.
Qed.
