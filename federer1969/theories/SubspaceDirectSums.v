(** Federer, Geometric measure theory (1969); page numbers are printed book
    pages. Scalar fields, generalisations and exceptional cases are governed
    by the explicit hypotheses below. Supporting steps are distinguished
    from statements printed in the book. Erratum reference:
    docs/references/federer-erratum.tex (May 1987), cited by erratum page
    and book page/line. *)

From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import InteriorDecomposition.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Federer 1.6.1, third corollary: T is the direct sum of P and Q
    exactly when its vectors are their sums and their intersection is
    the zero space. All three are actual subspaces of the ambient V. *)
(** Source for [subspace_direct_sum]: Federer (1969), 1.6.1, p. 24, third
    corollary. In words: The wedge of two nonzero simple vectors is nonzero
    exactly when its associated subspace is the direct sum of their
    associated subspaces. Definition or construction used to formalise this
    passage. *)
Definition subspace_direct_sum (K : fieldType) (V : lmodType K)
  (T P Q : subspace V) : Prop :=
  (forall v, T v <-> exists x y, P x /\ Q y /\ v=x+y) /\
  (forall v, P v -> Q v -> v=0).
