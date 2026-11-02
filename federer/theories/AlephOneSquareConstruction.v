(** Private transfinite construction for Federer (1969), 2.5.11, p. 102: the
    cardinal equation (card Y_1) times aleph-one equals aleph-one, used in
    the estimate card{(u,v): k(u,v) <= 0} <= aleph-one. Kelley, General
    Topology, Appendix, Definitions 175-176 and Theorems 177-180, pp.
    279-280 (Dover 2017 reprint of 1955), prove the general product law for
    infinite cardinals by exactly this order on pairs. We prove only the
    case needed here. A representative with countable proper initial
    segments is well ordered; its pairs are ordered by their larger
    coordinate and then by an auxiliary well ordering, so that every pair
    has only countably many predecessors. A fresh transfinite selection then
    injects the pairs into the representative. *)
From Corelib Require Import Init.Wf.
From mathcomp Require Import all_boot boolp classical_sets cardinality wochoice.
From Federer Require Import CardinalSuccessorUP CardinalInjection CardinalSuccessorPrefixes
  WellOrderLaws WellOrderRecursionBackground FreshTransfiniteSelectionConstruction
  WellFoundedLexicographic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Local Open Scope card_scope.

Section PairOrder.
Variable J : choiceType.
Variable r : rel J.
Hypothesis hr : well_order r.
Variable r2 : rel (J * J).
Hypothesis hr2 : well_order r2.
Variable C : set J.

(** Source for [pair_maximum]: supporting larger coordinate of a
    pair in the well ordering, for Federer 2.5.11, p. 102. *)
Definition pair_maximum (p : J * J) : J := if r p.1 p.2 then p.2 else p.1.

(** Source for [pair_maximum_left]: supporting bound of the first
    coordinate by the larger coordinate, Federer 2.5.11, p. 102. *)
Lemma pair_maximum_left p : r p.1 (pair_maximum p).
Proof.
rewrite /pair_maximum; case: ifPn=> // _.
exact: well_order_reflexive_law hr _.
Qed.

(** Source for [pair_maximum_right]: supporting bound of the second
    coordinate by the larger coordinate, Federer 2.5.11, p. 102. *)
Lemma pair_maximum_right p : r p.2 (pair_maximum p).
Proof.
rewrite /pair_maximum; case: ifPn=> h; first exact: well_order_reflexive_law hr _.
by have /orP[h1|h1] := well_order_total_law hr p.1 p.2; first by rewrite h1 in h.
Qed.

(** Source for [pair_before]: supporting order on pairs of the
    representative for Federer 2.5.11, p. 102: first by the larger
    coordinate, then by an auxiliary well ordering of pairs. *)
Definition pair_before (p q : J * J) : Prop :=
  (C p.1 /\ C p.2) /\ (C q.1 /\ C q.2) /\
  (strict_well_order_relation r (pair_maximum p) (pair_maximum q) \/
   (pair_maximum p = pair_maximum q /\ strict_well_order_relation r2 p q)).

(** Source for [pair_before_well_founded]: supporting well-foundedness
    of the pair order for the transfinite selection in Federer 2.5.11,
    p. 102; it is contained in a lexicographic pullback. *)
Lemma pair_before_well_founded : well_founded pair_before.
Proof.
have h1 := strict_well_order_well_founded hr.
have h2 := strict_well_order_well_founded hr2.
have hlex := lexicographic_well_founded h1 h2.
have hpull := well_founded_pullback (fun p : J * J => (pair_maximum p, p)) hlex.
by apply: well_founded_subrelation hpull=> p q [_ [_ h]].
Qed.

(** Source for [pair_before_total]: supporting comparability of
    distinct pairs of the representative, Federer 2.5.11, p. 102. *)
Lemma pair_before_total p q : C p.1 -> C p.2 -> C q.1 -> C q.2 -> p <> q ->
  pair_before p q \/ pair_before q p.
Proof.
move=> hp1 hp2 hq1 hq2 hne.
case: (pselect (pair_maximum p = pair_maximum q))=> [heq|hne'].
- have /orP[h|h] := well_order_total_law hr2 p q.
  + by left; split=> //; split=> //; right; split.
  + right; split=> //; split=> //; right; split; first by [].
    by split=> // h'; apply: hne; rewrite h'.
- have /orP[h|h] := well_order_total_law hr (pair_maximum p) (pair_maximum q).
  + by left; split=> //; split=> //; left; split.
  + right; split=> //; split=> //; left; split=> //.
    by move=> h'; apply: hne'; rewrite h'.
Qed.

(** Source for [pair_before_prefix_countable]: supporting countability
    of the predecessors of a pair when every proper initial segment of
    the representative is countable, Federer 2.5.11, p. 102. *)
Lemma pair_before_prefix_countable
    (hpre : forall x, C x -> countable (well_order_prefix C r x)) i :
  countable [set j | pair_before j i].
Proof.
case: (pselect (C i.1 /\ C i.2))=> [[hi1 hi2]|hni]; last first.
  have -> : [set j | pair_before j i] = set0.
    by apply/seteqP; split=> // j [_ [hi _]]; exact: hni hi.
  exact: countable0.
pose m := pair_maximum i.
have hm : C m by rewrite /m /pair_maximum; case: ifPn.
pose Q := [set y | C y /\ r y m].
have hQ : countable Q.
  have /countable_injP[e he] := hpre m hm.
  apply/countable_injP; exists (fun y => if y == m then 0%N else (e y).+1).
  move=> y z /set_mem [hy hym] /set_mem [hz hzm].
  case: ifPn=> [/eqP->|hyne]; case: ifPn=> [/eqP->|hzne] //.
  move=> [heq]; apply: he=> //; apply/mem_set; split=> //; split=> //; exact/eqP.
have hle : forall j, pair_before j i -> r (pair_maximum j) m.
  move=> j [_ [_ h]]; case: h=> [[h _]|[-> _]] //.
  exact: well_order_reflexive_law hr _.
have hsub : [set j | pair_before j i] `<=` Q `*` Q.
  move=> j hj; have [[hj1 hj2] _] := hj; split.
  - split=> //; exact: (well_order_transitive_law hr) (pair_maximum_left j) (hle j hj).
  - split=> //; exact: (well_order_transitive_law hr) (pair_maximum_right j) (hle j hj).
exact: sub_countable (subset_card_le hsub) (countableX hQ hQ).
Qed.

(** Source for [pair_fresh_selection]: supporting transfinite
    selection for Federer 2.5.11, p. 102: each pair receives a point
    of the uncountable representative distinct from the points of all
    its countably many predecessors. Kelley, Appendix, Theorem 128,
    pp. 270-271, is the recursion background. *)
Lemma pair_fresh_selection
    (hpre : forall x, C x -> countable (well_order_prefix C r x))
    (hC : ~ countable C) :
  exists F : J * J -> J, forall i, C (F i) /\ forall j, pair_before j i -> F i <> F j.
Proof.
have [c0 hc0] : exists c, C c.
  apply: contrapT=> hn; apply: hC.
  have -> : C = set0 by apply/seteqP; split=> // c hc; apply: hn; exists c.
  exact: countable0.
apply: (@well_founded_fresh_selection_exists (J * J) J pair_before (fun _ => C)
  pair_before_well_founded)=> i f.
pose g := fun j => if pselect (pair_before j i) is left h then f j h else c0.
pose U := g @` [set j | pair_before j i].
have hU : countable U.
  exact: sub_countable (card_image_le g _) (pair_before_prefix_countable hpre i).
have [x [hx hxU]] : exists x, C x /\ ~ U x.
  apply: contrapT=> hn; apply: hC; apply: sub_countable _ hU.
  apply: subset_card_le=> x hx; apply: contrapT=> hxU; apply: hn; by exists x.
exists x; split=> // j h heq; apply: hxU; exists j=> //.
rewrite /g; case: pselect=> [h'|hn]; last by case: (hn h).
by rewrite (Prop_irrelevance h' h) heq.
Qed.

(** Source for [pair_square_bound]: supporting injection of the
    pairs of the representative into the representative, Federer
    2.5.11, p. 102. *)
Lemma pair_square_bound
    (hpre : forall x, C x -> countable (well_order_prefix C r x))
    (hC : ~ countable C) :
  C `*` C #<= C.
Proof.
have [F hF] := pair_fresh_selection hpre hC.
apply: (@cardinal_bound_of_injection _ _ (C `*` C) C F).
- move=> p [hp1 hp2]; exact: (hF p).1.
- move=> p q /set_mem [hp1 hp2] /set_mem [hq1 hq2] heq.
  apply: contrapT=> hne.
  have [h|h] := pair_before_total hp1 hp2 hq1 hq2 hne.
  + exact: (hF q).2 p h (esym heq).
  + exact: (hF p).2 q h heq.
Qed.

End PairOrder.

(** Source for [aleph_one_square_bound]: the cardinal equation
    (card Y_1) times aleph-one equals aleph-one in Federer 2.5.11,
    p. 102, for a representative Y of the successor of aleph-zero:
    the Cartesian square of Y injects into Y. Kelley, Appendix,
    Theorems 179-180, pp. 279-280, state the general law for
    infinite cardinals; only this case is proved here. *)
Theorem aleph_one_square_bound (J : choiceType) (Y : set J) :
  is_cardinal_successor (@setT nat) Y -> Y `*` Y #<= Y.
Proof.
move=> hY.
have [r hr] := well_ordering_principle J.
have [r2 hr2] := well_ordering_principle (J * J)%type.
have [C [hCY [hYC hpre]]] := cardinal_successor_small_prefixes hY hr.
have hC : ~ countable C.
  move=> hc; have [_ [hn _]] := hY; apply: hn; exact: card_le_trans hYC hc.
have hsq := pair_square_bound hr hr2 hpre hC.
have [c0 hc0] : exists c, C c.
  apply: contrapT=> hn; apply: hC.
  have -> : C = set0 by apply/seteqP; split=> // c hc; apply: hn; exists c.
  exact: countable0.
have [e [he hinj]] := cardinal_injection_with_default c0 hYC.
have hYY : Y `*` Y #<= C `*` C.
  apply: (@cardinal_bound_of_injection _ _ (Y `*` Y) (C `*` C) (fun p => (e p.1, e p.2))).
  - move=> p [h1 h2]; split; exact: he.
  - move=> [a b] [c d] /set_mem [ha hb] /set_mem [hc hd] /= [h1 h2].
    have -> : a = c by exact: hinj _ _ (mem_set ha) (mem_set hc) h1.
    by have -> : b = d by exact: hinj _ _ (mem_set hb) (mem_set hd) h2.
exact: card_le_trans hYY (card_le_trans hsq (subset_card_le hCY)).
Qed.
