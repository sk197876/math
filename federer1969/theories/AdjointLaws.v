(** Federer (1969), 1.7.4, p. 30: adjoint identities needed for the
    projection factorisation in 1.7.3. All proofs use only the defining
    adjoint equation, without coordinates. *)
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import InnerProductUP InnerProductLaws Bilinear
  TensorUP AdjointUP SymmetricEndomorphisms.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [inner_vectors_ext]: Federer 1.7.4, p. 30,
    supporting uniqueness: equal inner products against every
    vector imply equality of the two vectors. *)
Lemma inner_vectors_ext (R : realFieldType) (V : lmodType R)
    (B : V -> V -> R) (hB : is_inner_product B) x y :
  (forall z, B z x = B z y) -> x = y.
Proof.
move=> h; apply/eqP; rewrite -subr_eq0; apply/eqP.
apply: (@inner_right_separates R V B hB) => z.
by rewrite (bilBr (inner_bilinear hB)) h subrr.
Qed.

(** Source for [adjoint_unique]: Federer 1.7.4, p. 30,
    the adjoint is uniquely determined by its defining equation. *)
Theorem adjoint_unique (R : realFieldType) (V U : lmodType R)
    (B : V -> V -> R) (C : U -> U -> R) (hB : is_inner_product B)
    (f : {linear V -> U}) (g h : {linear U -> V}) :
  is_adjoint B C f g -> is_adjoint B C f h -> g =1 h.
Proof.
move=> hg hh y; apply: (@inner_vectors_ext R V B hB) => x.
by rewrite hg hh.
Qed.

(** Source for [adjoint_reverse]: Federer 1.7.4, p. 30,
    f is an adjoint of f*, giving the double-adjoint identity
    whenever both adjoints are defined. *)
Theorem adjoint_reverse (R : realFieldType) (V U : lmodType R)
    (B : V -> V -> R) (C : U -> U -> R)
    (hB : is_inner_product B) (hC : is_inner_product C)
    (f : {linear V -> U}) (g : {linear U -> V}) :
  is_adjoint B C f g -> is_adjoint C B g f.
Proof.
move=> hg y x; rewrite (inner_symmetric hC) -hg.
exact (@inner_symmetric R V B hB x (g y)).
Qed.

(** Source for [adjoint_composition]: Federer 1.7.4, p. 30,
    the adjoint of g composed with f is f* composed with g*. *)
Theorem adjoint_composition (R : fieldType) (V U W : lmodType R)
    (B : V -> V -> R) (C : U -> U -> R) (D : W -> W -> R)
    (f : {linear V -> U}) (g : {linear U -> W})
    (a : {linear U -> V}) (b : {linear W -> U}) :
  is_adjoint B C f a -> is_adjoint C D g b ->
  is_adjoint B D (linear_comp g f) (linear_comp a b).
Proof.
move=> ha hb x z; change (B x (a (b z)) = D (g (f x)) z).
by rewrite ha hb.
Qed.

(** Source for [symmetric_self_adjoint]: Federer 1.7.4,
    p. 30, a symmetric map is its own adjoint. *)
Lemma symmetric_self_adjoint (R : fieldType) (V : lmodType R)
    (B : V -> V -> R) (f : {linear V -> V}) :
  is_symmetric_endomorphism B f -> is_adjoint B B f f.
Proof. by move=> hf x y; rewrite hf. Qed.
