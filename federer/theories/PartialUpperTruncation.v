(** Federer (1969), proof of 2.4.11, p. 86: the bounded functions
    gn(x)=inf{|f(x)|,n} increase to |f|. We index positive integers by n+1
    and give a general upper-truncation operation retaining the original
    partial domain. The local erratum has no correction for this theorem. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import ExtendedRealOrderTopology PartialFunctionUP PartialFunctionPostcomposition.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [partial_upper_truncation]: the truncation
    used in Federer 2.4.11, proof p. 86,
    stated for a general extended-real ceiling. The proof
    applies it to |f| at the positive ceilings n+1. *)
Definition partial_upper_truncation (R : realType) (X : Type)
    (f : partial_function X (extended_real_line R)) (c : \bar R) :=
  partial_function_postcompose f (fun y => (Order.min y c : extended_real_line R)).

(** Source for [partial_upper_truncation_domain]: supporting domain
    preservation of gn in Federer 2.4.11, proof p. 86 *)
Lemma partial_upper_truncation_domain (R : realType) (X : Type)
    (f : partial_function X (extended_real_line R)) c :
  partial_function_domain (partial_upper_truncation f c)=partial_function_domain f.
Proof. exact: partial_function_postcompose_domain. Qed.
