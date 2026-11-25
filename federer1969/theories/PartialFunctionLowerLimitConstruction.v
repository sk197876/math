(** Federer (1969), 2.3.2, p. 74: lower limit on the eventual common domain. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import PartialFunctionUP ExtendedRealOrderTopology ExtendedRealBounds
  PartialFunctionLimitExtremaUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [partial_function_lower_limit_witness]: private
    existence construction for Federer 2.3.2, p. 74,
    using the sealed scalar supimum of eventual lower bounds. *)
Definition partial_function_lower_limit_witness (R : realType) (X : Type)
    (f : nat -> partial_function X (extended_real_line R)) : partial_function X (extended_real_line R).
Proof.
refine (@Build_partial_function X (extended_real_line R)
  (fun x y => partial_function_eventual_domain f x /\
    y = extended_real_sup (partial_function_eventual_lower_bound f x)) _).
by move=> x y z [_ ->] [_ ->].
Defined.

(** Source for [partial_function_lower_limit_exists]: existence
    of the abstract lower limit in Federer 2.3.2, p. 74,
    including infinite values and arbitrary partial input domains. *)
Theorem partial_function_lower_limit_exists (R : realType) (X : Type)
    (f : nat -> partial_function X (extended_real_line R)) :
  exists g, is_partial_function_lower_limit f g.
Proof.
exists (partial_function_lower_limit_witness f); constructor.
- apply/seteqP; split=> x.
  + by move=> [y [hx _]].
  + move=> hx; exists (extended_real_sup (partial_function_eventual_lower_bound f x)); by split.
- move=> x y [_ ->] b hb; exact: extended_real_sup_upper hb.
- move=> x y [_ ->] b hb; exact: extended_real_sup_least hb.
Qed.
