(** Federer (1969), 1.7.1, p. 28, final sentence. This interface combines
    the two proved implications. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import InnerProductUP InnerBoundedness
  InnerFiniteCompactness InnerCompactDimension LinearBasis.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Source for [inner_boundedly_compact_iff_finite_basis]: Federer
    1.7.1, p. 28, final assertion, in words: the metric inner-product
    space is boundedly compact exactly when its dimension is finite.
    Finite dimension is expressed by existence of a finite basis;
    no finite-dimensional structure is assumed on the ambient space.
    Real completeness is required only for the forward compactness proof. *)
Theorem inner_boundedly_compact_iff_finite_basis (R : realType)
    (V : lmodType R) (B : V -> V -> R) (hB : is_inner_product B) :
  inner_boundedly_compact hB <-> exists n (e : 'I_n -> V), is_basis e.
Proof.
split; first exact: inner_boundedly_compact_finite_basis.
move=> [n [e he]]; exact: inner_finite_basis_boundedly_compact he.
Qed.
