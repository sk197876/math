(** Federer (1969), 2.5.7, p. 99: strict increase of the weighted sum
    defining r in the p=1 case. This supporting summation lemma isolates
    that order step, using 2.1.1(9), p. 53. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal.
From Federer Require Import NonnegativeSum NonnegativeSumSupport NonnegativeSumRestriction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [strict_nonnegative_sum_comparison]: supporting strict
    weighted-sum comparison in Federer 2.5.7, p. 99 Only the smaller sum
    must be finite; the larger sum may be infinite. *)
Theorem strict_nonnegative_sum_comparison (R : realType) (I : choiceType)
    (A : set I) (f g : I -> \bar R) (j : I) :
  A j -> (forall i, A i -> 0 <= f i) -> (forall i, A i -> 0 <= g i) ->
  (forall i, A i -> f i <= g i) -> f j < g j ->
  nonnegative_sum A f < +oo -> nonnegative_sum A f < nonnegative_sum A g.
Proof.
move=> hj hf hg hfg hstrict hfin.
have hi : A `&` [set j]=[set j].
  apply/seteqP; split; first by move=> x [_ hx].
  move=> x hx; split=> //; by rewrite hx.
have hfrest : nonnegative_sum (A `\` [set j]) f \is a fin_num.
  rewrite (ge0_fin_numE (nonnegative_sum_nonnegative _ _)).
  apply: le_lt_trans _ hfin; apply: nonnegative_sum_subset=> x [hx _]; exact: hx.
have hrest : nonnegative_sum (A `\` [set j]) f <= nonnegative_sum (A `\` [set j]) g.
  apply: nonnegative_sum_mono=> x [hx _]; exact: hfg x hx.
rewrite (@nonnegative_sum_split R I A [set j] f hf)
  (@nonnegative_sum_split R I A [set j] g hg) hi (@nonnegative_sum_singleton R I f j (hf j hj))
  (@nonnegative_sum_singleton R I g j (hg j hj)).
exact: lte_leD hfrest hstrict hrest.
Qed.
