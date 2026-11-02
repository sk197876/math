(** Federer (1969), 2.6.5, p. 119: finite Cartesian products defined
    inductively. We specify one left association by abstract binary product
    laws; existence and independence arguments are separate. Stage n has n+1
    factors, indexed 0 through n, so the base stage is the original first
    measure. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal.
From Federer Require Import MeasureUP ProductMeasureUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [finite_cartesian_carrier]: the iterated
    Cartesian product underlying Federer 2.6.5, p. 119,
    with stage n representing the first n+1 factors. The
    carrier records the domains, just as binary products do. *)
Fixpoint finite_cartesian_carrier (X : nat -> choiceType) (n : nat) : choiceType :=
  match n with
  | 0 => X 0%N
  | k.+1 => [the choiceType of (finite_cartesian_carrier X k * X k.+1)%type]
  end.

(** Source for [is_finite_cartesian_measure_family]: abstract inductive laws
    for the finite products of Federer 2.6.5, p. 119 This fixes one
    association without claiming unconditional associativity. *)
Record is_finite_cartesian_measure_family (R : realType) (X : nat -> choiceType)
    (alpha : forall j, set (X j) -> \bar R)
    (nu : forall n, set (finite_cartesian_carrier X n) -> \bar R) : Prop := {
  (** Source for [finite_cartesian_first_law]: the one-factor
      base of the induction in Federer 2.6.5, p. 119. *)
  finite_cartesian_first_law : nu 0%N = alpha 0%N;
  (** Source for [finite_cartesian_successor_law]: binary-product
      step of the induction in Federer 2.6.5, p. 119,
      specified by the extremal law of 2.6.1, p. 115. *)
  finite_cartesian_successor_law : forall n,
    is_product_measure (nu n) (alpha n.+1) (nu n.+1)
}.

(** Source for [finite_cartesian_family_unique]: supporting uniqueness of
    the fixed-association family in Federer 2.6.5, p. 119 (. *)
Theorem finite_cartesian_family_unique (R : realType) (X : nat -> choiceType)
    (alpha : forall j, set (X j) -> \bar R)
    (nu eta : forall n, set (finite_cartesian_carrier X n) -> \bar R) :
  is_finite_cartesian_measure_family alpha nu ->
  is_finite_cartesian_measure_family alpha eta -> nu = eta.
Proof.
move=> hn he; apply: functional_extensionality_dep=> n; elim: n=> [|n ih].
- by rewrite (finite_cartesian_first_law hn) (finite_cartesian_first_law he).
- have hp := finite_cartesian_successor_law hn n.
  rewrite ih in hp; exact: product_measure_unique hp (finite_cartesian_successor_law he n).
Qed.
