(** Supporting Federer (1969), 3.3.6, p. 293:
    apply 2.8.4–2.8.5 with diameter weight
    and tau= 2 to the positive radius balls.
    The diameter enlargement estimate gives
    the fivefold cover. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  cardinality reals constructive_ereal topology lra.
From Federer Require Import MetricClosedBalls CoveringFamilyUP CoveringFamilyLaws
  CountablyClosedFamilyUP DiametricRegularityUP DiameterWeightLaws
  WeightedCoverSelectionUP WeightedCoverSelection WeightedEnlargements BallEnlargementBound DisjointDenseBallFamilies CardinalInjection
  SeparableClosedCover.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [indexed_bounded_radius_disjoint_fivefold_cover]:
    the countable D selected by 2.8.5 in Federer 3.3.6, p. 293.
    Indices remain the original source points even if projected centers
    coincide; disjoint positive balls force injectivity on D. The proof
    expands the same weighted selection of 2.8.4–2.8.5, pp. 143–144. *)
Theorem indexed_bounded_radius_disjoint_fivefold_cover (R : realType)
    (X : metricType R) (I : choiceType) (U : set I) (c : I->X) (h : I->R) :
  (exists T : set X, countable T /\ dense T) ->
  (forall x, U x -> 0<h x) ->
  (exists M : R, forall x, U x -> h x<=M) ->
  exists D : set I,
    D `<=` U /\ countable D /\
    (forall s t, D s -> D t -> s<>t ->
      metric_closed_ball (c s) (h s) `&` metric_closed_ball (c t) (h t)=set0) /\
    (forall s t, D s -> D t -> c s=c t -> s=t) /\
    c @` U `<=` \bigcup_(s in D) metric_closed_ball (c s) (5*h s).
Proof.
move=>[T [hTc hTd]] hp [M hM].
case: (pselect (exists x, U x))=>[[x0 hx0]|hempty].
- pose F := [set B : set X | exists x, U x /\ B=metric_closed_ball (c x) (h x)].
  have hbounded B : F B -> metric_set_bounded B.
    move=>[x [hx ->]]; exact: (covering_closed_ball_bounded (c x) (ltW (hp x hx))).
  have [w hw] := real_diameter_weight_exists hbounded.
  have hnonempty B : F B -> B<>set0.
    move=>[x [hx ->]] he.
    have hm : metric_closed_ball (c x) (h x) (c x).
      by rewrite /metric_closed_ball /= mdistxx; exact: (ltW (hp x hx)).
    by rewrite he in hm.
  have hwn B : F B -> 0<=w B := fun hB=>diameter_weight_nonnegative hw hB.
  have hwb : exists C : R, forall B, F B -> w B<=C.
    exists (M+M)=>B hB; have [x [hx he]] := hB.
    have hFb : F (metric_closed_ball (c x) (h x)) by rewrite -he.
    rewrite he; apply: (le_trans (diameter_weight_ball_bound hw hFb (ltW (hp x hx)))).
    exact: (lerD (hM x hx) (hM x hx)).
  have hTau : (1:R)<2 by rewrite ltr1n.
  pose G := weighted_cover_selection hnonempty hwn hwb hTau.
  have hG : is_weighted_cover_selection F w 2 G :=
    weighted_cover_selection_specification hnonempty hwn hwb hTau.
  have hGF : G `<=` F := weighted_selection_members hG.
  have hex B : exists x, F B -> U x /\ B=metric_closed_ball (c x) (h x).
    case: (pselect (F B))=>[hB|hn].
    + have [x hx] := hB; by exists x.
    + exists x0; by move=>/hn.
  have [index hi] := choice hex.
  pose D := index @` G.
  have hDU : D `<=` U.
    move=>s [B hB <-]; exact: (hi B (hGF B hB)).1.
  have hdis s t : D s -> D t -> s<>t ->
      metric_closed_ball (c s) (h s) `&` metric_closed_ball (c t) (h t)=set0.
    move=>[B hB <-] [C hC <-] hne.
    have hBC : B<>C by move=>he; apply: hne; by rewrite he.
    rewrite -(hi B (hGF B hB)).2 -(hi C (hGF C hC)).2.
    exact: (weighted_selection_disjoint hG hB hC hBC).
  have hGc : countable G.
    apply: (disjoint_family_meeting_countable_set
      (weighted_selection_disjoint hG) hTc).
    move=>B hB; have [i [hiU ->]]:=hGF B hB.
    have [t [htT hnear]]:=@metric_dense_point_near R X T hTd (c i) (h i) (hp i hiU).
    exists t; split; first exact:htT.
    exact:ltW hnear.
  exists D; split; first exact:hDU.
  split; first exact:(sub_countable (card_image_le index G) hGc).
  split; first exact:hdis.
  split.
  + move=>s t hs ht he; apply:contrapT=>hne.
    have hBoth:(metric_closed_ball (c s) (h s) `&` metric_closed_ball (c t) (h t)) (c s).
      split; rewrite /metric_closed_ball /=; first by rewrite mdistxx; exact:ltW (hp s (hDU s hs)).
      by rewrite he mdistxx; exact:ltW (hp t (hDU t ht)).
    by rewrite (hdis s t hs ht hne) in hBoth.
  + move=>z [x hx <-].
    have hBx : F (metric_closed_ball (c x) (h x)) by exists x.
    have hmember : metric_closed_ball (c x) (h x) (c x).
      by rewrite /metric_closed_ball /= mdistxx; exact: (ltW (hp x hx)).
    have hcover := weighted_selection_enlargement_cover hG.
    have hballunion : (\bigcup_(B in F) B) (c x) by exists (metric_closed_ball (c x) (h x)).
    have [B hB hhat] := hcover (c x) hballunion.
    exists (index B); first by exists B.
    have [hindex he] := hi B (hGF B hB).
    have hFB : F (metric_closed_ball (c (index B)) (h (index B))).
      by rewrite -he; exact: (hGF B hB).
    have htwo : (0:R)<= 2 by rewrite ler0n.
    have hinc := diameter_enlargement_ball_bound hw htwo hFB (ltW (hp _ hindex)).
    have halg : (1+2*2)*h (index B)= 5*h (index B) by lra.
    rewrite halg in hinc.
    apply: hinc; by rewrite -he.
- exists set0; split; first by move=>x [].
  split; first exact:countable0.
  split; first by move=>s t [].
  split; first by move=>s t [].
  move=>z [x hx _]; exfalso; apply:hempty; by exists x.
Qed.
