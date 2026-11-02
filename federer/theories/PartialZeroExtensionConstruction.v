(** Private existence construction for the zero extension in Federer (1969),
    2.4.10, p. 85. The specification precedes the graph implementation;
    downstream results use only its sealed laws. Source context:
    PartialZeroExtensionUP.v. *)
From mathcomp Require Import all_boot classical_sets.
From Federer Require Import PartialFunctionUP PartialZeroExtensionUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [partial_zero_extension_witness]: private graph
    construction establishing existence of f_A in Federer
    2.4.10, p. 85. *)
Definition partial_zero_extension_witness (X Y : Type) (zero : Y)
    (A : set X) (f : partial_function X Y) : partial_function X Y.
Proof.
refine (@Build_partial_function X Y
  (fun x y => (A x /\ partial_function_graph f x y) \/ (~ A x /\ y=zero)) _).
move=> x y z [[hx hy]|[hx hy]] [[hx' hz]|[hx' hz]].
- exact: partial_function_single_valued hy hz.
- by exfalso; exact: hx' hx.
- by exfalso; exact: hx hx'.
- by rewrite hy hz.
Defined.

(** Source for [partial_zero_extension_exists]: proved existence
    of the abstract zero extension in Federer 2.4.10, p. 85. *)
Lemma partial_zero_extension_exists (X Y : Type) (zero : Y)
    (A : set X) (f : partial_function X Y) :
  exists g, is_partial_function_zero_extension zero A f g.
Proof. exists (partial_zero_extension_witness zero A f); by move=> x y. Qed.
