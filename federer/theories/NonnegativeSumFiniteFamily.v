(** Federer (1969), 2.1.1(2), p. 52: finite iteration of additivity. This
    supports grouping sums in (9), p. 53. editions: NonnegativeSumUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra finmap boolp
  classical_sets reals constructive_ereal.
From Federer Require Import NonnegativeSum NonnegativeSumSupport NonnegativeSumAdd.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [nonnegative_sum_finite_family]: Federer
    2.1.1(2), p. 52; supporting exchange of an arbitrary nonnegative
    sum with a finite sum, proved by induction on the finite sequence. *)
Lemma nonnegative_sum_finite_family (R : realType) (I : choiceType)
    (J : eqType) (A : set I) (s : seq J) (f : J -> I -> \bar R) :
  (forall j, j \in s -> forall x, A x -> 0 <= f j x) ->
  nonnegative_sum A (fun x => \sum_(j <- s) f j x) =
    \sum_(j <- s) nonnegative_sum A (f j).
Proof.
elim: s=> [|j s ih] hf.
- rewrite big_nil; apply: nonnegative_sum_zero=> x _; exact: big_nil.
- have hj : forall x, A x -> 0 <= f j x by apply: hf; rewrite in_cons eqxx.
  have hs : forall k, k \in s -> forall x, A x -> 0 <= f k x.
    move=> k hk; apply: hf; by rewrite in_cons hk orbT.
  have he : nonnegative_sum A (fun x => \sum_(k <- j :: s) f k x) =
      nonnegative_sum A (fun x => f j x + \sum_(k <- s) f k x).
    apply: nonnegative_sum_ext=> x _; by rewrite big_cons.
  rewrite he big_cons nonnegative_sum_add //.
  + by rewrite ih.
  + move=> x hx; rewrite big_seq; apply: sume_ge0=> k hk; exact: (hs k hk x hx).
Qed.
