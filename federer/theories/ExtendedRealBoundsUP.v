(** Federer (1969), 2.1.1, p. 51: every extended-real set has a supremum and
    an infimum, including the empty set. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals constructive_ereal.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [is_extended_real_supremum]: Federer 2.1.1,
    p. 51, third paragraph; abstract least-upper-bound specification
    for arbitrary subsets of the extended reals. *)
Record is_extended_real_supremum (R : realType) (S : set (\bar R)) c : Prop := {
  extended_real_supremum_upper : forall x, S x -> x <= c;
  extended_real_supremum_least : forall d, (forall x, S x -> x <= d) -> c <= d
}.

(** Source for [extended_real_supremum_unique]: Federer 2.1.1,
    p. 51, third paragraph; supporting uniqueness by antisymmetry. *)
Lemma extended_real_supremum_unique (R : realType) (S : set (\bar R)) c d :
  is_extended_real_supremum S c -> is_extended_real_supremum S d -> c = d.
Proof.
move=> hc hd; apply/eqP; rewrite eq_le; apply/andP; split.
- exact: (extended_real_supremum_least hc (extended_real_supremum_upper hd)).
- exact: (extended_real_supremum_least hd (extended_real_supremum_upper hc)).
Qed.
