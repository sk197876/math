(** Federer (1969), 2.1.2, pp. 53-54: supporting treatment of repeated
    members in a countable covering family. Grouping is Federer 2.1.1(9), p.
    53 *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals constructive_ereal.
From Federer Require Import NonnegativeSum NonnegativeSumGrouping.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [nonnegative_sum_image_bound]: Federer
    2.1.2, p. 53, supporting comparison of a family with an indexed
    enumeration: repeated images can only increase a nonnegative sum. *)
Lemma nonnegative_sum_image_bound (R : realType) (I J : choiceType)
    (A : set I) (h : I -> J) (g : J -> \bar R) :
  (forall x, A x -> 0 <= g (h x)) ->
  nonnegative_sum (h @` A) g <= nonnegative_sum A (fun x => g (h x)).
Proof.
move=> hg; rewrite (@nonnegative_sum_grouping R I J A (h @` A) h); last 2 first.
- by move=> x hx; exists x.
- exact hg.
apply: nonnegative_sum_mono=> y [x hx <-].
apply: nonnegative_sum_term; split; first exact hx; exact: eqxx.
Qed.
