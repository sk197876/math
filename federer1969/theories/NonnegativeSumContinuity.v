(** Federer (1969), 2.1.1(13), p. 53: increasing exhaustion of the summation
    set, first for nonnegative terms. editions: NonnegativeSumUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra finmap boolp
  classical_sets reals constructive_ereal.
From Federer Require Import ExtendedRealBounds ExtendedRealOrderLimit NonnegativeSum.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [finite_increasing_cover]: Federer 2.1.1(13), p. 53 Every
    finite set covered by an increasing sequence lies in a single member. *)
Lemma finite_increasing_cover (I : eqType) (B : nat -> set I) (s : seq I) :
  (forall n m, (n <= m)%N -> B n `<=` B m) ->
  (forall x, x \in s -> exists n, B n x) ->
  exists n, forall x, x \in s -> B n x.
Proof.
move=> hm; elim: s=> [|a s ih] hc.
- exists 0%N; by move=> x; rewrite in_nil.
- have [n hn] := hc a (mem_head a s).
  have htail : forall x, x \in s -> exists n, B n x.
    move=> x hx; apply: hc; by rewrite in_cons hx orbT.
  have [m hmt] := ih htail; exists (maxn n m)=> x.
  rewrite in_cons => /orP[/eqP->|hx].
  + exact: (hm n (maxn n m) (leq_maxl n m) a hn).
  + exact: (hm m (maxn n m) (leq_maxr n m) x (hmt x hx)).
Qed.

(** Source for [nonnegative_sum_increasing_supremum]: Federer
    2.1.1(13), p. 53; the nonnegative sums over an increasing
    exhaustion have supremum the sum over the union. This is the
    order-theoretic part of the asserted monotone convergence. *)
Theorem nonnegative_sum_increasing_supremum (R : realType) (I : choiceType)
    (A : set I) (B : nat -> set I) (f : I -> \bar R) :
  (forall n m, (n <= m)%N -> B n `<=` B m) ->
  (forall n, B n `<=` A) ->
  (forall x, A x -> exists n, B n x) ->
  nonnegative_sum A f = extended_real_sup [set t | exists n, t = nonnegative_sum (B n) f].
Proof.
move=> hm hsub hcover; apply/eqP; rewrite eq_le; apply/andP; split.
- apply: nonnegative_sum_least=> C hC.
  have [n hn] : exists n, forall x, x \in C -> B n x.
    apply: finite_increasing_cover hm _ => x hx; exact: hcover (hC x hx).
  apply: le_trans (@nonnegative_sum_upper R I (B n) f C hn) _.
  apply: extended_real_sup_upper; by exists n.
- apply: extended_real_sup_least=> t [n ->]; exact: nonnegative_sum_subset (hsub n).
Qed.

(** Source for [nonnegative_sum_increasing_limit]: Federer 2.1.1(13), p. 53,
    nonnegative case; the sums increase to the sum on the union, with
    convergence in the extended order topology. *)
Theorem nonnegative_sum_increasing_limit (R : realType) (I : choiceType)
    (A : set I) (B : nat -> set I) (f : I -> \bar R) :
  (forall n m, (n <= m)%N -> B n `<=` B m) ->
  (forall n, B n `<=` A) ->
  (forall x, A x -> exists n, B n x) ->
  extended_increases_to (fun n => nonnegative_sum (B n) f) (nonnegative_sum A f).
Proof.
move=> hm hsub hc; rewrite (nonnegative_sum_increasing_supremum f hm hsub hc).
apply: extended_increasing_limit=> n m hnm; exact: nonnegative_sum_subset (hm n m hnm).
Qed.
