(** Private graph construction for the pointwise numerical sum supporting
    Federer (1969), 2.4.8, p. 84. Single-valuedness follows from
    numerical-sum extensionality and the single-valued summand graphs.
    Source context and precise signed-family extension:
    PartialNumericalSumUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import ExtendedRealOrderTopology PartialFunctionUP NumericalSum NumericalSumValues PartialNumericalSumUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [partial_numerical_sum_witness]: private existence
    construction for the abstract pointwise sum in Federer
    2.4.8, p. 84; undefined signed sums remain absent. *)
Definition partial_numerical_sum_witness (R : realType) (X : Type) (J : choiceType)
    (D : set J) (f : J -> partial_function X (extended_real_line R)) :
    partial_function X (extended_real_line R).
Proof.
refine (@Build_partial_function X (extended_real_line R)
  (fun x z => exists u : J -> \bar R,
    (forall j, D j -> partial_function_graph (f j) x (u j)) /\ numerical_sum D u = Some z) _).
move=> x a b [u [hu ha]] [v [hv hb]].
have he : numerical_sum D u = numerical_sum D v.
  apply: numerical_sum_ext=> j hj; exact: partial_function_single_valued (hu j hj) (hv j hj).
rewrite he hb in ha; by case: ha.
Defined.

(** Source for [partial_numerical_sum_exists]: proved existence
    of the pointwise sum specified for Federer 2.4.8, p. 84. *)
Theorem partial_numerical_sum_exists (R : realType) (X : Type) (J : choiceType)
    (D : set J) (f : J -> partial_function X (extended_real_line R)) :
  exists g, is_partial_function_numerical_sum D f g.
Proof. exists (partial_numerical_sum_witness D f); by move=> x z. Qed.
