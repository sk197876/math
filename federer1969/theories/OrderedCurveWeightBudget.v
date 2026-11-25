(** Federer (1969), 3.3.19, p. 304:
    the finite cyclic boundary estimate, expressed on
    a list in its actual boundary-parameter order.
    Only finite algebra and the variation supremum are used. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology lra ring.
From Federer Require Import CurveVariationUP ExtendedRealBounds.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section Budget.
Variable R:realType.
Variable Y:metricType R.
Variable I:eqType.
Variable g:R->Y.
Variable t:I->R.
Variable w:I->R.

(** Source for [ordered_curve_chain_weight_budget]:
    supporting finite sum of adjacent endpoint weights
    in the cyclic estimate of 3.3.19, p. 304.
    The two unpaired end weights are retained explicitly. *)
Lemma ordered_curve_chain_weight_budget (i:I) (s:seq I):
  uniq (i::s) ->
  (forall j k,j \in i::s ->k \in i::s ->j!=k ->w j+w k<=mdist (g (t j)) (g (t k))) ->
  2*(\sum_(j<-i::s) w j)<=
    chain_sum g (map t (i::s))+w i+w (last i s).
Proof.
elim:s i=>[|j s ih] i /= hUnique hPair.
- rewrite !big_cons big_nil /=;lra.
- move/andP:hUnique=>[hi hRest].
  have hPairRest j' k':j' \in j::s ->k' \in j::s ->j'!=k' ->
      w j'+w k'<=mdist (g (t j')) (g (t k')).
    move=>hj hk hDifferent;apply:hPair=>//;by rewrite inE ?hj ?hk orbT.
  have hInduction:=ih j hRest hPairRest.
  have hDifferent:i!=j.
    apply/negP=>/eqP hEqual;move:hi;by rewrite hEqual inE eqxx.
  have hJ:j \in i::j::s by rewrite !inE eqxx orbT.
  have hEdge:=hPair i j (mem_head i (j::s)) hJ hDifferent.
  rewrite big_cons /= in hInduction *.
  lra.
Qed.
End Budget.
