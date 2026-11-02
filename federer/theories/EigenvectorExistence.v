(** Federer (1969), 1.7.3, p. 29: nonzero eigenvectors used to bound the
    dimensions of minimal invariant subspaces. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import InnerProductUP InnerProductLaws Bilinear
  SymmetricEndomorphisms SymmetricEigenbasis EigenbasisUP LinearBasis
  OrthonormalFamilies Annihilator Hom.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [basis_nonzero_positive_dimension]: Federer
    1.7.3, p. 29, supporting observation: a space containing a
    nonzero vector cannot have an empty basis. *)
Lemma basis_nonzero_positive_dimension (R : fieldType) (V : lmodType R)
    n (b : 'I_n -> V) (hb : is_basis b) :
  (exists x : V, x != 0) -> (0 < n)%N.
Proof.
move=> [x hx]; case: n b hb => [|n] b hb //.
have he := basis_vector_expansion hb x.
by rewrite big_ord0 in he; move: hx; rewrite he eqxx.
Qed.

(** Source for [symmetric_unit_eigenvector]: Federer 1.7.3,
    p. 29, supporting consequence of the orthonormal eigenbasis:
    in positive finite dimension a symmetric map has a unit eigenvector. *)
Theorem symmetric_unit_eigenvector (R : realType) (V : lmodType R)
    (B : V -> V -> R) (hB : is_inner_product B)
    (f : {linear V -> V}) (hf : is_symmetric_endomorphism B f)
    n (b : 'I_n -> V) (hb : is_basis b) : (0 < n)%N ->
  exists x : V, exists lambda : R, B x x = 1 /\ f x = lambda *: x.
Proof.
move=> hn; have [e [lambda he]] :=
  @symmetric_orthonormal_eigenbasis R V B hB f hf n b hb.
pose i : 'I_n := Ordinal hn.
exists (e i), (lambda i); split.
- by rewrite (eigenbasis_orthonormal he) eqxx.
- exact (@eigenbasis_eigenvalue R V B f n e lambda he i).
Qed.

(** Source for [unit_square_nonzero]: Federer 1.7.3, p. 29,
    supporting nonvanishing of the unit eigenvectors. *)
Lemma unit_square_nonzero (R : realFieldType) (V : lmodType R)
    (B : V -> V -> R) (hB : is_inner_product B) x :
  B x x = 1 -> x != 0.
Proof.
move=> hx; rewrite -(inner_positive hB) hx; exact: ltr01.
Qed.
