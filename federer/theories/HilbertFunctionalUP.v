(** Federer (1969), 1.7.13, p. 37: representation of a continuous linear
    functional by inner product with one vector. The equation is specified
    independently of its existence proof. No finite-dimensional hypothesis
    is imposed. Supporting nearest point reference and Source context:
    HilbertSpaceUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import InnerProductUP InnerProductLaws Bilinear.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [is_hilbert_functional_vector]: Federer 1.7.13,
    p. 37, final assertion: the vector u satisfies f(v)=u.v
    for every v. This specification does not presume that f has
    a representative. *)
Definition is_hilbert_functional_vector (R : realFieldType) (V : lmodType R)
    (B : V -> V -> R) (f : {linear V -> R^o}) (u : V) : Prop :=
    forall v, f v = B u v.

(** Source for [hilbert_functional_vector_unique]: Federer
    1.7.13, p. 37, uniqueness of u. Nondegeneracy suffices;
    completeness and continuity are needed only for existence. *)
Theorem hilbert_functional_vector_unique (R : realFieldType) (V : lmodType R)
    (B : V -> V -> R) (hB : is_inner_product B) (f : {linear V -> R^o}) u w :
    is_hilbert_functional_vector B f u -> is_hilbert_functional_vector B f w -> u=w.
Proof.
move=> hu hw.
have hz : u-w= 0.
  apply: (inner_left_separates hB) => v.
  by rewrite (bilBl (inner_bilinear hB)) -hu -hw subrr.
apply/eqP; by rewrite -subr_eq0 hz eqxx.
Qed.
