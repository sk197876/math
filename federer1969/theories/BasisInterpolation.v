(** Federer (1969), 1.7.3, p. 30: specifying linear maps g and h by their
    values on the orthonormal basis. This uses the already proved abstract
    basis-coordinate laws, without inspecting their construction. *)
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import LinearBasis TensorUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [basis_interpolation]: Federer 1.7.3, p. 30,
    supporting definition of a linear map with prescribed values
    on a basis. Existence follows from the basis universal property. *)
Definition basis_interpolation (R : fieldType) (I : choiceType)
    (V U : lmodType R) (e : I -> V) (he : is_basis e) (d : I -> U) :
    {linear V -> U} := linear_comp (basis_synthesis d) (basis_coordinates he).

(** Source for [basis_interpolationE]: Federer 1.7.3,
    p. 30, the interpolated map takes each basis vector to
    its prescribed image. *)
Lemma basis_interpolationE (R : fieldType) (I : choiceType)
    (V U : lmodType R) (e : I -> V) (he : is_basis e) (d : I -> U) i :
  basis_interpolation he d (e i) = d i.
Proof.
change (basis_synthesis d (basis_coordinates he (e i)) = d i).
by rewrite basis_coordinatesE basis_synthesisE.
Qed.
