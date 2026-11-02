(** Federer (1969), 2.10.8, p. 175: equivalence of the printed
    countable-family covering hypothesis and the indexed specification used
    by the existing construction. Repeated image sets cannot decrease a
    nonnegative numerical sum. This uses 2.1.1(9), p. 53 *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  cardinality reals constructive_ereal topology.
From Federer Require Import NonnegativeSum NonnegativeSumImageBound TopologicalBorel BorelCoverCostUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [borel_cover_cost_family_inequality]: direct
    printed countable-family hypothesis in Federer 2.10.8,
    p. 175, as a consequence of the indexed specification. *)
Lemma borel_cover_cost_family_inequality (R : realType) (X : topologicalType)
    (c : set X -> \bar R) (hc : is_borel_cover_cost c)
    (A : set X) (G : set (set X)) :
  countable G -> borel_set A -> (forall B, G B -> borel_set B) ->
  A `<=` \bigcup_(B in G) B -> c A<=nonnegative_sum G c.
Proof.
exact: (@borel_cover_cost_cover R X c hc [the choiceType of set X] G (fun B => B) A).
Qed.

(** Source for [borel_cover_cost_of_family_inequality]: supporting
    converse equivalence with the printed hypothesis of Federer
    2.10.8, p. 175. The indexed formulation adds no assumption:
    take the countable image family and use the nonnegative-sum
    bound for repetitions. Nonnegative Borel costs are inherited
    from the construction's standing hypotheses in 2.10.1. *)
Lemma borel_cover_cost_of_family_inequality (R : realType) (X : topologicalType)
    (c : set X -> \bar R) :
  (forall A, borel_set A -> 0<=c A) ->
  (forall A G, countable G -> borel_set A -> (forall B, G B -> borel_set B) ->
    A `<=` \bigcup_(B in G) B -> c A<=nonnegative_sum G c) ->
  is_borel_cover_cost c.
Proof.
move=> hnon hcover; constructor; first exact hnon.
move=> J D S A hD hA hS hcov.
have hG : countable (S @` D) := sub_countable (card_image_le S D) hD.
have hB B : (S @` D) B -> borel_set B by move=> [j hj <-]; exact: hS.
have hcov' : A `<=` \bigcup_(B in S @` D) B.
  move=> x hx; have [j hj hxj] := hcov x hx.
  exists (S j); last exact hxj; by exists j.
apply: le_trans (hcover A (S @` D) hG hA hB hcov') _.
apply: nonnegative_sum_image_bound=> j hj; exact: hnon (hS j hj).
Qed.

(** Source for [borel_cover_cost_empty]: supporting empty-cover
    consequence of the hypothesis in Federer 2.10.8, p. 175.
    The empty Borel set has zero cost, so allowing empty
    partition cells does not alter their cost sums. *)
Lemma borel_cover_cost_empty (R : realType) (X : topologicalType)
    (c : set X -> \bar R) (hc : is_borel_cover_cost c) : c set0=0.
Proof.
have h0 : borel_set (@set0 X) := open_borel_set open0.
apply/eqP; rewrite eq_le (@borel_cover_cost_nonnegative R X c hc set0 h0) andbT.
have hb := @borel_cover_cost_family_inequality R X c hc set0 set0 (countable0 (set X)) h0
  (fun _ h => False_rect _ h) (fun _ h => False_rect _ h).
by rewrite nonnegative_sum_empty in hb.
Qed.
