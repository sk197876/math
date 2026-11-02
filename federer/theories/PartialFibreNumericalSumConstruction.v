(** Private existence proof for the fibre sum in Federer (1969), 3.2.3(2), p. 243. Single-valuedness follows from the summand graph and numerical-sum extensionality. Only the sealing module and assumptions audit may import this witness. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import ExtendedRealOrderTopology PartialFunctionUP NumericalSum NumericalSumValues PartialFibreNumericalSumUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [partial_fibre_numerical_sum_witness]: private
    existence witness for the exact fibre sum of Federer
    3.2.3(2), p. 243. Uniqueness uses only the original
    graph's single-valuedness and numerical-sum extensionality. *)
Definition partial_fibre_numerical_sum_witness (R:realType) (X:choiceType) (Y:Type)
    (p:X->Y) (u:partial_function X (extended_real_line R)):
    partial_function Y (extended_real_line R).
Proof.
refine (@Build_partial_function Y (extended_real_line R)
  (fun y z=>exists w:X->\bar R,
    (forall x,p x=y -> partial_function_graph u x (w x)) /\
    numerical_sum [set x|p x=y] w=Some z) _).
move=>y a b [w [hw ha]] [v [hv hb]].
have he:numerical_sum [set x|p x=y] w=numerical_sum [set x|p x=y] v.
  apply:numerical_sum_ext=>x hx; exact:partial_function_single_valued (hw x hx) (hv x hx).
rewrite he hb in ha; by case:ha.
Defined.

(** Source for [partial_fibre_numerical_sum_exists]: proved
    existence of the graph specified for the inner sum
    in Federer 3.2.3(2), p. 243. *)
Theorem partial_fibre_numerical_sum_exists (R:realType) (X:choiceType) (Y:Type)
    (p:X->Y) (u:partial_function X (extended_real_line R)):
  exists v,is_partial_fibre_numerical_sum p u v.
Proof. exists (partial_fibre_numerical_sum_witness p u); by move=>y z. Qed.
