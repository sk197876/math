(** Federer (1969), 2.4.10, p. 85, and 2.4.18(1), p. 90:
    a subset integral under composition uses the actual inverse
    image of its subset. This supporting graph law retains all
    missing values of the original partial function. *)
From mathcomp Require Import all_boot classical_sets.
From Federer Require Import PartialFunctionUP PartialFunctionPrecomposition PartialZeroExtension.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [partial_zero_extension_precompose_graph]:
    the inverse-image cutoff for composition in 2.4.18(1), p. 90,
    with the subset convention of 2.4.10, p. 85. Supporting
    change of parameter for Federer 3.2.46, p. 281. *)
Lemma partial_zero_extension_precompose_graph (X Y Z : Type)
    (u : X -> Y) (zero : Z) (A : set Y) (f : partial_function Y Z) x z :
  partial_function_graph (partial_function_precompose u
    (partial_function_zero_extension zero A f)) x z <->
  partial_function_graph (partial_function_zero_extension zero (u @^-1` A)
    (partial_function_precompose u f)) x z.
Proof.
have hF := @partial_function_zero_extension_graph Y Z zero A f (u x) z.
have hG := @partial_function_zero_extension_graph X Z zero (u @^-1` A)
  (partial_function_precompose u f) x z.
split=> h; [exact: hG.2 (hF.1 h) | exact: hF.2 (hG.1 h)].
Qed.
