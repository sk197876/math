(** Federer (1969), 2.4.17, p. 90: local exponent brackets for continuity.
    This supporting order argument chooses endpoints in the exponent set for
    an arbitrary sequence tending to a point of that set. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal.
From Federer Require Import ExtendedRealOrderLimit.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [real_sequence_eventual_bracket]: supporting exponent bracket
    for the Lebesgue-convergence argument of Federer 2.4.17, p. 90 This
    general order fact does not require convexity of the set. *)
Lemma real_sequence_eventual_bracket (R : realType) (A : set R) (p : nat -> R) q :
  A q -> (forall n, A (p n)) -> extended_order_limit (fun n => (p n)%:E) q%:E ->
  exists s t k, A s /\ A t /\ (s <= q)%R /\ (q <= t)%R /\
    forall n, (k <= n)%N -> (s <= p n)%R /\ (p n <= t)%R.
Proof.
move=> hq hp hl.
have hleft : exists s k, A s /\ (s <= q)%R /\ forall n, (k <= n)%N -> (s <= p n)%R.
  have [he|he] := pselect (exists j, (p j < q)%R).
  - have [j hj] := he; have [k hk] := hl.1 (p j)%:E hj.
    exists (p j),k; split; first exact: hp.
    split; first exact: ltW hj.
    move=> n hn; exact: ltW (hk n hn).
  - exists q,0%N; split=> //; split=> // n hn; rewrite leNgt; apply/negP=> hb; apply: he; by exists n.
have hright : exists t k, A t /\ (q <= t)%R /\ forall n, (k <= n)%N -> (p n <= t)%R.
  have [he|he] := pselect (exists j, (q < p j)%R).
  - have [j hj] := he; have [k hk] := hl.2 (p j)%:E hj.
    exists (p j),k; split; first exact: hp.
    split; first exact: ltW hj.
    move=> n hn; exact: ltW (hk n hn).
  - exists q,0%N; split=> //; split=> // n hn; rewrite leNgt; apply/negP=> hb; apply: he; by exists n.
have [s [k [hs [hsq hsp]]]] := hleft; have [t [j [ht [hqt hpt]]]] := hright.
exists s,t,(maxn k j); split=> //; split=> //; split=> //; split=> // n hn; split.
- exact: hsp n (leq_trans (leq_maxl k j) hn).
- exact: hpt n (leq_trans (leq_maxr k j) hn).
Qed.
