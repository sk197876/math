(** Federer (1969), 2.1.1, p. 51: increasing and decreasing extended-real
    limits. Source context: ExtendedRealPartial.v. The interval criterion
    below expresses convergence in the order topology directly, including
    one-sided neighborhoods at both infinite endpoints. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals constructive_ereal.
From Federer Require Import ExtendedRealBoundsUP ExtendedRealBounds.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [extended_order_limit]: Federer 2.1.1, p. 51,
    opening and fourth paragraphs; order-topology convergence:
    eventually above every strict lower bound on the limit and
    below every strict upper bound. At infinity only one side matters. *)
Definition extended_order_limit (R : realType) (u : nat -> \bar R) l :=
  (forall a, a < l -> exists N, forall n, (N <= n)%N -> a < u n) /\
  (forall b, l < b -> exists N, forall n, (N <= n)%N -> u n < b).

(** Source for [extended_increases_to]: Federer 2.1.1, p. 51,
    fourth paragraph; nondecreasing sequence with the specified limit. *)
Definition extended_increases_to (R : realType) (u : nat -> \bar R) l :=
  (forall n m, (n <= m)%N -> u n <= u m) /\ extended_order_limit u l.

(** Source for [extended_decreases_to]: Federer 2.1.1, p. 51,
    fourth paragraph; nonincreasing sequence with the specified limit. *)
Definition extended_decreases_to (R : realType) (u : nat -> \bar R) l :=
  (forall n m, (n <= m)%N -> u m <= u n) /\ extended_order_limit u l.

(** Source for [extended_increasing_supremum_limit]: Federer 2.1.1, p. 51
    and (13), p. 53; supporting monotone convergence from the
    least-upper-bound property. *)
Theorem extended_increasing_supremum_limit (R : realType) (u : nat -> \bar R) l :
  (forall n m, (n <= m)%N -> u n <= u m) ->
  is_extended_real_supremum [set t | exists n, t = u n] l ->
  extended_increases_to u l.
Proof.
move=> hm hl; split; first exact hm.
split.
- move=> a ha; have [he|he] := pselect (exists N, a < u N).
  + have [N hN] := he; exists N=> n hn; exact: lt_le_trans hN (hm N n hn).
  + exfalso; have hla : l <= a.
      apply: (extended_real_supremum_least hl)=> t [n ->].
      rewrite leNgt; apply/negP=> hlt; apply: he; by exists n.
    by move: ha; rewrite ltNge hla.
- move=> b hb; exists 0%N=> n _; apply: le_lt_trans _ hb.
  apply: (extended_real_supremum_upper hl); by exists n.
Qed.

(** Source for [extended_increasing_limit]: Federer 2.1.1,
    p. 51, supporting theorem: every nondecreasing extended-real
    sequence converges to the supremum of its range. *)
Lemma extended_increasing_limit (R : realType) (u : nat -> \bar R) :
  (forall n m, (n <= m)%N -> u n <= u m) ->
  extended_increases_to u (extended_real_sup [set t | exists n, t = u n]).
Proof.
move=> hm; apply: extended_increasing_supremum_limit hm _; constructor.
- exact: extended_real_sup_upper.
- exact: extended_real_sup_least.
Qed.
