(** Private graph witness for the inversion operation
    of Federer (1969), 3.1.11, p. 220. *)
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import AlgebraUP PartialFunctionUP AlgebraInverseUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Source for [algebra_inverse_graph_exists]:
    the inverse relation is an exact partial function,
    supporting Federer 3.1.11, p. 220. *)
Theorem algebra_inverse_graph_exists (K : fieldType) (A : algebra K) :
  exists F : partial_function A A, is_algebra_inverse_graph F.
Proof.
exists (@Build_partial_function A A (@is_two_sided_algebra_inverse K A)
  (@two_sided_algebra_inverse_unique K A)).
by move=> x y.
Qed.
