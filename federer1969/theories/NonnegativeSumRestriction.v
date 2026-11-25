(** Federer (1969), 2.1.1(3), p. 52: restricting a summation set is
    equivalent to extending the summand by zero. Supporting lemmas for the
    grouping assertion (9), p. 53. editions: NonnegativeSumUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra finmap boolp
  classical_sets reals constructive_ereal.
From Federer Require Import NonnegativeSum NonnegativeSumSupport NonnegativeSumAdd.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope fset_scope.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [nonnegative_sum_restrict]: Federer 2.1.1(3),
    p. 52; supporting identity obtained by intersecting each finite
    summation set with B. No finiteness is imposed on B. *)
Lemma nonnegative_sum_restrict (R : realType) (I : choiceType)
    (A B : set I) (f : I -> \bar R) :
  nonnegative_sum A (fun x => if x \in B then f x else 0) =
  nonnegative_sum (A `&` B) f.
Proof.
apply/eqP; rewrite eq_le; apply/andP; split.
- apply: nonnegative_sum_least=> C hC.
  rewrite -big_mkcond big_fset_condE.
  apply: nonnegative_sum_upper=> x; rewrite inE => /andP[hx /set_mem hBx].
  split; [exact: hC | exact hBx].
- apply: nonnegative_sum_least=> C hC.
  have he : (\sum_(x <- C) f x) =
      \sum_(x <- C) (if x \in B then f x else 0).
    apply: eq_big_seq=> x hx; by rewrite (mem_set (hC x hx).2).
  rewrite he; apply: nonnegative_sum_upper=> x hx; exact: (hC x hx).1.
Qed.

(** Source for [nonnegative_sum_split]: Federer 2.1.1(9),
    p. 53, supporting grouping into a set and its complement.
    Additivity is applied to the two functions extended by zero. *)
Lemma nonnegative_sum_split (R : realType) (I : choiceType)
    (A B : set I) (f : I -> \bar R) :
  (forall x, A x -> 0 <= f x) ->
  nonnegative_sum A f = nonnegative_sum (A `&` B) f + nonnegative_sum (A `\` B) f.
Proof.
move=> hf.
have he : nonnegative_sum A f = nonnegative_sum A
    (fun x => (if x \in B then f x else 0) + (if x \in ~` B then f x else 0)).
  apply: nonnegative_sum_ext=> x hx; rewrite in_setC.
  by case: (x \in B); rewrite ?adde0 ?add0e.
rewrite he nonnegative_sum_add.
- by rewrite !nonnegative_sum_restrict.
- move=> x hx; case: ifP=> _; [exact: hf | exact: lexx].
- move=> x hx; case: ifP=> _; [exact: hf | exact: lexx].
Qed.
