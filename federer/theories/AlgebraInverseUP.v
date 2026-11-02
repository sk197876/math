(** Federer (1969), 3.1.11, p. 220:
    inversion is a partial operation on the automorphisms.
    The supporting algebraic specification records both
    inverse identities and never assigns a value elsewhere. *)
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import AlgebraUP PartialFunctionUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Source for [is_two_sided_algebra_inverse]: the
    inverse identities underlying the inversion operator
    in Federer 3.1.11, p. 220. This supporting
    definition applies to any unital associative algebra. *)
Definition is_two_sided_algebra_inverse (K : fieldType) (A : algebra K) (x y : A) :=
  alg_mul A x y=alg_one A /\ alg_mul A y x=alg_one A.

(** Source for [is_algebra_inverse_graph]: exact domain
    and values of the partial inversion operation,
    supporting Federer 3.1.11, p. 220. *)
Definition is_algebra_inverse_graph (K : fieldType) (A : algebra K)
    (F : partial_function A A) :=
  forall x y, partial_function_graph F x y <-> is_two_sided_algebra_inverse x y.

(** Source for [two_sided_algebra_inverse_unique]:
    two-sided inverses are unique, supporting the
    inversion notation in Federer 3.1.11, p. 220. *)
Lemma two_sided_algebra_inverse_unique (K : fieldType) (A : algebra K) (x y z : A) :
  is_two_sided_algebra_inverse x y -> is_two_sided_algebra_inverse x z -> y=z.
Proof.
move=> [hxy hyx] [hxz hzx].
by rewrite -(@alg_unitr K A y) -hxz alg_assoc hyx alg_unitl.
Qed.
