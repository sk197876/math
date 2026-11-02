(** Federer (1969), 2.4.6, p. 84: the scalar lower limit of the integral
    values in Fatou's lemma. The order specification is the supremum of
    eventual lower bounds, consistent with the partial-function lower-limit
    laws used for 2.3.2, p. 74, and the complete extended line of 2.1.1, p.
    51. This is supporting scalar infrastructure, not an additional
    assertion attributed to Fatou. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal.
From Federer Require Import ExtendedRealBoundsUP ExtendedRealOrderLimit ExtendedRealLimitBounds.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [extended_eventual_lower_bounds]: supporting
    eventual lower bounds for the scalar lower limit in
    Federer 2.4.6, p. 84. *)
Definition extended_eventual_lower_bounds (R : realType) (u : nat -> \bar R) :=
  [set b | exists N, forall n, (N <= n)%N -> b <= u n].

(** Source for [is_extended_lower_limit]: abstract scalar
    lower-limit specification supporting Federer 2.4.6, p. 84;
    supremum convention from 2.1.1, p. 51. *)
Definition is_extended_lower_limit (R : realType) (u : nat -> \bar R) l :=
  is_extended_real_supremum (extended_eventual_lower_bounds u) l.

(** Source for [extended_lower_limit_unique]: supporting
    uniqueness of the scalar lower limit in Federer 2.4.6,
    p. 84, from the abstract supremum laws. *)
Lemma extended_lower_limit_unique (R : realType) (u : nat -> \bar R) a b :
  is_extended_lower_limit u a -> is_extended_lower_limit u b -> a = b.
Proof. exact: extended_real_supremum_unique. Qed.

(** Source for [extended_lower_limit_eventual_bound]: every
    eventual lower bound is at most the lower limit; supporting
    the eventual comparisons in Federer 2.4.6, proof p. 84. *)
Lemma extended_lower_limit_eventual_bound (R : realType) (u : nat -> \bar R) l b :
  is_extended_lower_limit u l -> extended_eventual_lower_bounds u b -> b <= l.
Proof. move=> hl hb; exact (@extended_real_supremum_upper R _ l hl b hb). Qed.

(** Source for [extended_lower_limit_increasing_comparison]: supporting
    passage to the limit of increasing lower bounds in Federer 2.4.6, p. 84;
    no finiteness of the limit is required. *)
Lemma extended_lower_limit_increasing_comparison (R : realType)
    (u v : nat -> \bar R) l a :
  is_extended_lower_limit u l -> extended_increases_to v a ->
  (forall n, v n <= u n) -> a <= l.
Proof.
move=> hl [hm hv] h; apply: (@extended_order_limit_upper_bound R v a l hv)=> n.
apply: (extended_lower_limit_eventual_bound hl); exists n=> m hnm.
exact: le_trans (hm n m hnm) (h m).
Qed.
