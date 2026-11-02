(** Federer (1969), 3.2.22(2), p. 258: assemble
    countably rectifiable coordinate fibres and their null
    remainders. The laws are direct consequences of
    3.2.14(3), p. 251, and countable null unions. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets cardinality constructive_ereal topology.
From Federer Require Import RectifiableSetUP RectifiableElementary CountablyRectifiableUnions
  MeasureUP MeasureBasic MeasureAlmostUP MeasureAlmostBasic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [countably_measure_rectifiable_null]: null
    fibre remainders in Federer 3.2.22(2), p. 258,
    are countably (phi,m) rectifiable by 3.2.14(3),
    p. 251, using the empty rectifiable cover. *)
Lemma countably_measure_rectifiable_null (R:realType) (X:metricType R)
    (phi:set X->\bar R) m (N:set X):
  is_measure phi ->phi N=0 ->is_countably_measure_m_rectifiable phi m N.
Proof.
move=>hm hN; split; first exact hm; exists set0; split.
- exact:countably_rectifiable_empty.
- by rewrite /measure_almost_included setD0.
Qed.

(** Source for [countably_measure_rectifiable_subset]:
    restrictions of coordinate fibres in Federer 3.2.22(2),
    p. 258, preserve countable (phi,m) rectifiability.
    Keep the same rectifiable cover; its omitted subset
    is null by monotonicity, without measurability assumptions. *)
Lemma countably_measure_rectifiable_subset (R:realType) (X:metricType R)
    (phi:set X->\bar R) m (E F:set X):
  F `<=` E ->is_countably_measure_m_rectifiable phi m E ->
  is_countably_measure_m_rectifiable phi m F.
Proof.
move=>hFE [hm [C [hC hNull]]]; split; first exact hm.
exists C; split; first exact hC.
apply:(measure_null_subset hm _ hNull)=>x [hx hNot]; split; first exact:(hFE x hx); exact hNot.
Qed.

(** Source for [countably_measure_rectifiable_countable_union]:
    the countable source-chart fibre union in Federer
    3.2.22(2), p. 258, from 3.2.14(2)–(3),
    p. 251. Countably unite the actual rectifiable
    covers and their null omitted sets. No finiteness
    of the union's mass is asserted by this lemma. *)
Theorem countably_measure_rectifiable_countable_union (R:realType) (X:metricType R)
    (I:choiceType) (phi:set X->\bar R) m (D:set I) (F:I->set X):
  is_measure phi ->countable D ->
  (forall i,D i ->is_countably_measure_m_rectifiable phi m (F i)) ->
  is_countably_measure_m_rectifiable phi m (\bigcup_(i in D) F i).
Proof.
move=>hm hCount hF.
have hex i:exists C:set X,is_countably_m_rectifiable m C /\ (D i ->phi (F i `\` C)=0).
  have [hi|hi]:=pselect (D i).
  - have [_ [C [hC hNull]]]:=hF i hi; exists C; split; first exact hC.
    by move=>_.
  - exists set0; split; first exact:countably_rectifiable_empty.
    by move=>/hi.
have [C hC]:=choice hex.
split; first exact hm; exists (\bigcup_(i in D) C i); split.
- exact:(countably_rectifiable_countable_union hCount (fun i _=>(hC i).1)).
- have hNull:phi (\bigcup_(i in D) (F i `\` C i))=0.
    exact:(measure_null_countable_union hm hCount (fun i hi=>(hC i).2 hi)).
  apply:(measure_null_subset hm _ hNull)=>x [[i hi hFx] hNot].
  exists i; first exact hi; split; first exact hFx.
  move=>hCx; apply:hNot; by exists i.
Qed.
