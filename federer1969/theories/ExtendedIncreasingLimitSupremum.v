(** Supporting scalar order facts for Federer (1969), 2.4.8, p. 84: finite
    nonnegative sums increase to the full numerical sum by 2.1.1(13), p. 53,
    and this limit is their lower limit for application of 2.4.7. Source
    context: PartialNumericalSumUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal.
From Federer Require Import ExtendedRealOrderTopology ExtendedRealBoundsUP ExtendedRealOrderLimit ExtendedRealLimitBounds ExtendedLowerLimitUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [extended_increasing_limit_supremum]: supporting
    supremum characterization of the increasing sum limit used
    in Federer 2.4.8, p. 84. *)
Lemma extended_increasing_limit_supremum (R : realType) (u : nat -> \bar R) a :
  extended_increases_to u a -> is_extended_real_supremum [set b | exists n, b = u n] a.
Proof.
move=> [hm hl]; constructor.
- move=> b [n ->]; rewrite leNgt; apply/negP=> han.
  have [N hN] := hl.2 (u n) han.
  have hh := hN (maxn N n) (leq_maxl N n).
  by move: hh; rewrite ltNge (hm n (maxn N n) (leq_maxr N n)).
- move=> b hb; apply: (@extended_order_limit_upper_bound R u a b hl)=> n.
  apply: hb; by exists n.
Qed.

(** Source for [extended_increasing_limit_lower_limit_laws]:
    the increasing scalar limit in Federer 2.4.8, p. 84,
    satisfies the lower-limit specification required by 2.4.7. *)
Lemma extended_increasing_limit_lower_limit_laws (R : realType) (u : nat -> \bar R) a :
  extended_increases_to u a -> is_extended_lower_limit u a.
Proof.
move=> hlim; have hsup := extended_increasing_limit_supremum hlim; constructor.
- move=> b [N hN]; apply: le_trans (hN N (leqnn N)) _.
  apply: (extended_real_supremum_upper hsup); by exists N.
- move=> b hb; apply: (extended_real_supremum_least hsup)=> c [n ->].
  apply: hb; exists n=> m hnm; exact: hlim.1 n m hnm.
Qed.

(** Source for [extended_order_limit_unique]: uniqueness of
    the scalar limit used to identify the two sides of Federer
    2.4.8, p. 84. Infinite endpoints are retained. *)
Lemma extended_order_limit_unique (R : realType) (u : nat -> \bar R) a b :
  extended_order_limit u a -> extended_order_limit u b -> a = b.
Proof.
move=> ha hb; apply/eqP; rewrite eq_le; apply/andP; split.
- rewrite leNgt; apply/negP=> hba.
  have [q [hbq hqa]] := @extended_rationals_order_dense R b a hba.
  have [N hN] := ha.1 _ hqa; have [M hM] := hb.2 _ hbq.
  have hh := lt_trans (hN (maxn N M) (leq_maxl N M)) (hM (maxn N M) (leq_maxr N M)).
  by move: hh; rewrite ltxx.
- rewrite leNgt; apply/negP=> hab.
  have [q [haq hqb]] := @extended_rationals_order_dense R a b hab.
  have [N hN] := hb.1 _ hqb; have [M hM] := ha.2 _ haq.
  have hh := lt_trans (hN (maxn N M) (leq_maxl N M)) (hM (maxn N M) (leq_maxr N M)).
  by move: hh; rewrite ltxx.
Qed.
