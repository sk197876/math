(** Federer (1969), 2.10.47(2), pp. 204–205: if gamma_(i+1)(S intersect E)
    is at most zeta(S) for every S in H_i, then gamma_(i+1)(E)=gamma_i(E).
    The printed proof uses (1). Here a direct covering comparison proves the
    same assertion for arbitrary refining covering families, without a
    boundary-null hypothesis. This supporting strengthening retains the
    book's contents and local cost hypothesis. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal.
From Federer Require Import RefiningCoverContent MeasureUP MeasureBasic MeasureRestriction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [refining_content_successor_stability]: direct
    generalised form of 2.10.47(2), pp. 204–205.
    Restrict the finer content to E and bound it on every
    coarser eligible generator: the new hypothesis handles
    level i and the generator law handles later levels. *)
Theorem refining_content_successor_stability (R : realType) (X : choiceType)
    H cost i gamma eta (E : set X) :
  @is_refining_cover_content R X H cost i gamma ->
  is_refining_cover_content H cost i.+1 eta ->
  (forall S, refining_cover_tail H i S -> 0<=cost S) ->
  (forall S, H i S -> eta (S `&` E)<=cost S) -> eta E=gamma E.
Proof.
move=> hg he hc hlocal.
have hi : (i<=i.+1)%N := leqnSn i.
have htail S : refining_cover_tail H i.+1 S -> refining_cover_tail H i S.
  move=> [j [hj hS]]; exists j; split=> //; exact: leq_trans hi hj.
have hm := refining_cover_content_measure he (fun S hS=>hc S (htail S hS)).
apply/eqP; rewrite eq_le (refining_cover_content_nondecreasing hg he hc hi) andbT.
have hbound : forall S, refining_cover_tail H i S ->
    measure_restrict eta E S<=cost S.
  move=> S [j [hij hS]].
  case: (eqVneq j i)=> [hji|hji].
  - rewrite /measure_restrict setIC; apply: hlocal; by rewrite -hji.
  - have hnext : (i.+1<=j)%N by rewrite ltn_neqAle eq_sym hji hij.
    have ht : refining_cover_tail H i.+1 S by exists j; split.
    rewrite /measure_restrict.
    apply: le_trans (@measure_mono R X eta hm (E `&` S) S (fun x hx=>hx.2)) _.
    exact: refining_cover_content_generator he ht (hc S (htail S ht)).
have hh := refining_cover_content_comparison hg (measure_restrict_is_measure hm E) hbound E.
by rewrite /measure_restrict setIid in hh.
Qed.
