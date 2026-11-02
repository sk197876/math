(** Federer (1969), 2.10.28, p. 193: specify f(x) as the finite measure of
    the closed lower half-line. For the Cantor function the measure is H^m
    restricted to A(m,n). *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory.
Local Open Scope classical_set_scope.

(** Source for [is_finite_cumulative_function]: direct
    cumulative-value equation for f in 2.10.28,
    p. 193, for a finite measure on R.
    This specifies the function before choosing
    any real-valued representative. *)
Definition is_finite_cumulative_function (R : realType) (mu : set R -> \bar R) (f : R -> R) :=
  forall x : R, mu [set z | (z<=x)%R]=(f x)%:E.

(** Source for [finite_cumulative_function_unique]: supporting
    uniqueness of f defined by the measure
    equation in 2.10.28, p. 193. *)
Lemma finite_cumulative_function_unique (R : realType) (mu : set R -> \bar R) f g :
  is_finite_cumulative_function mu f -> is_finite_cumulative_function mu g -> f=g.
Proof.
move=> hf hg; apply/funext=> x; apply: EFin_inj; by rewrite -(hf x) -(hg x).
Qed.
