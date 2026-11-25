(** Federer (1969), Corollary 2.8.6, p. 144: removing finitely many selected
    closed sets leaves a target covered by the other enlargements. The proof
    uses only fineness, finite closed unions, and the abstract
    weighted-selection laws. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets cardinality reals topology.
From Federer Require Import CoveringFamilyUP WeightedCoverSelectionUP
  WeightedEnlargements.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [fine_cover_avoids_finite_closed_union]: the first sentence
    of the proof of Federer 2.8.6, p. 144 Outside a finite closed union, an
    open ball avoids it, so a sufficiently small fine covering member also
    avoids it. *)
Lemma fine_cover_avoids_finite_closed_union (R : realType) (X : metricType R)
    (F H : set (set X)) (A : set X) :
  family_covers_finely F A -> finite_set H ->
  (forall S, H S -> closed S) -> forall x,
  (A `\` \bigcup_(S in H) S) x -> exists T,
    F T /\ T x /\ T `&` (\bigcup_(S in H) S) = set0.
Proof.
move=> hf hH hclosed x [hA hx].
have hc : closed (\bigcup_(S in H) S).
  exact (@closed_bigcup X [the choiceType of set X] H idfun hH hclosed).
have ho := closed_openC hc.
have hn : nbhs x (~` \bigcup_(S in H) S).
  rewrite openE in ho; exact: ho x hx.
have [e he hb] := proj1 (metricType_numDomainType.nbhs_mdistP x _) hn.
have [T [hT [ht hsub]]] := hf x hA e he.
exists T; split=> //; split=> //.
apply/seteqP; split=> [y [hy hu]|y []].
exfalso; exact ((hb y (hsub y hy)) hu).
Qed.

(** Source for [weighted_selection_finite_remainder_cover]: direct
    formalisation of Federer 2.8.6, p. 144 The finite H lies in the selected
    family G. Every target point outside union H lies in the enlargement of
    a member of G minus H. No target measurability or countability of G is
    imposed. *)
Theorem weighted_selection_finite_remainder_cover (R : realType) (X : metricType R)
    (F : set (set X)) (d : set X -> R) (tau : R)
    (G : set (set X)) (A : set X) :
  (forall S, F S -> closed S) -> family_covers_finely F A ->
  is_weighted_cover_selection F d tau G ->
  forall H, finite_set H -> H `<=` G ->
  (A `\` \bigcup_(S in H) S) `<=`
    \bigcup_(S in G `\` H) weighted_enlargement F d tau S.
Proof.
move=> hclosed hf hG H hH hHG x hx.
have hHC S (hS : H S) : closed S.
  exact: hclosed S (@weighted_selection_members R X F d tau G hG S (hHG S hS)).
have [T [hT [ht havoid]]] := @fine_cover_avoids_finite_closed_union R X F H A
  hf hH hHC x hx.
have [S [hS [hmeet hweight]]] := @weighted_selection_dominates R X F d tau G hG T hT.
have hnot : ~ H S.
  move=> hSH; apply: hmeet; apply/seteqP; split=> [y [hy hs]|y []].
  have hu : (\bigcup_(B in H) B) y by exists S.
  have hbad : (T `&` \bigcup_(B in H) B) y by split.
  by rewrite havoid in hbad.
exists S; first by split.
exact (@weighted_enlargement_contains_member R X F d tau T S hT hmeet hweight x ht).
Qed.
