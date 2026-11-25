(** Federer (1969), 3.1.11, p. 220:
    public exact laws of the partial inversion operation,
    used without access to its graph construction. *)
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import AlgebraUP PartialFunctionUP AlgebraInverseUP AlgebraInverseSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Source for [algebra_inverse]: the partial inverse
    operation supporting Federer 3.1.11, p. 220. *)
Definition algebra_inverse (K : fieldType) (A : algebra K) : partial_function A A :=
  @AlgebraInverse.value K A.

(** Source for [algebra_inverse_graph]: exact inverse
    identities for the public graph, supporting Federer
    3.1.11, p. 220. *)
Lemma algebra_inverse_graph (K : fieldType) (A : algebra K) x y :
  partial_function_graph (algebra_inverse A) x y <->
    is_two_sided_algebra_inverse x y.
Proof. exact: (@AlgebraInverse.laws K A x y). Qed.

(** Source for [algebra_inverse_domain]: inversion is
    defined precisely on invertible algebra elements,
    supporting Federer 3.1.11, p. 220. *)
Lemma algebra_inverse_domain (K : fieldType) (A : algebra K) x :
  partial_function_domain (algebra_inverse A) x <->
    exists y, is_two_sided_algebra_inverse x y.
Proof.
split=> [[y hy]|[y hy]]; exists y;
  [exact: (algebra_inverse_graph x y).1 hy|exact: (algebra_inverse_graph x y).2 hy].
Qed.

(** Source for [algebra_inverse_involutive]: inverting
    an inverse returns the original element, supporting
    the inverse operation in Federer 3.1.11, p. 220. *)
Lemma algebra_inverse_involutive (K : fieldType) (A : algebra K) x y :
  partial_function_graph (algebra_inverse A) x y ->
  partial_function_graph (algebra_inverse A) y x.
Proof.
move/(algebra_inverse_graph x y)=> [hxy hyx].
apply/(algebra_inverse_graph y x); by split.
Qed.

(** Source for [algebra_inverse_identity]: the algebra
    unit is its own inverse, supporting the series
    in Federer 3.1.11, p. 220. *)
Lemma algebra_inverse_identity (K : fieldType) (A : algebra K) :
  partial_function_graph (algebra_inverse A) (alg_one A) (alg_one A).
Proof. apply/algebra_inverse_graph; split; exact: alg_unitl. Qed.
