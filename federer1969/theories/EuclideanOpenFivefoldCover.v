(** Federer (1969), 3.1.20, p. 232: the open fivefold balls
    Q_i cover the union of the coordinate neighbourhoods. This
    supporting strengthening of 3.1.13 uses the same diameter
    selection with tau=2, exploiting Euclidean ball diameters. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology lra.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric
  FiniteCoordinates MetricClosedBalls MetricDiameterUP MetricDiameter EuclideanBallDiameter
  CoveringFamilyUP CoveringFamilyLaws CountablyClosedFamilyUP DiametricRegularityUP
  DiameterWeightLaws WeightedCoverSelectionUP WeightedCoverSelection.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [diameter_weight_euclidean_ball]: supporting the
    open Q_i cover in Federer 3.1.20, p. 232. In positive ambient
    dimension the selected diameter weight equals twice the radius,
    by the proved Euclidean diameter theorem of 2.10.2. *)
Lemma diameter_weight_euclidean_ball (R:realType) n
    (F:set (set (inner_metric_space (@euclidean_inner_productP R n.+1)))) w
    (hw:is_real_diameter_weight F w) a r :
  F (metric_closed_ball a r) -> 0<=r -> w (metric_closed_ball a r)=r+r.
Proof.
move=>hF hr.
have he:=metric_diameter_unique (hw _ hF)
  (extended_metric_diameter_specification (metric_closed_ball a r)).
rewrite (euclidean_closed_ball_diameter a hr) in he.
by move: he=>/eqP; rewrite eqe=>/eqP.
Qed.

(** Source for [euclidean_positive_radius_open_fivefold_cover]:
    the disjoint closed balls with an open fivefold cover used in
    Federer 3.1.20, p. 232, obtained by the 2.8.4 selection as
    in 3.1.13, p. 224. In positive Euclidean dimension the center
    of each original ball is within three selected radii, so the
    printed fivefold cover is strict. *)
Theorem euclidean_positive_radius_open_fivefold_cover (R:realType) n
    (U:set (inner_metric_space (@euclidean_inner_productP R n.+1)))
    (h:inner_metric_space (@euclidean_inner_productP R n.+1)->R) :
  (forall x, U x -> 0<h x) -> (exists M:R, forall x, U x -> h x<=M) ->
  exists S:set (inner_metric_space (@euclidean_inner_productP R n.+1)),
    S `<=` U /\
    (forall s t, S s -> S t -> s<>t ->
      metric_closed_ball s (h s) `&` metric_closed_ball t (h t)=set0) /\
    U `<=` \bigcup_(s in S) [set x|mdist s x<5*h s].
Proof.
move=>hp [M hM].
pose X:=inner_metric_space (@euclidean_inner_productP R n.+1).
case: (pselect (exists x,U x))=>[[x0 hx0]|hempty].
- pose F:= [set B:set X|exists x,U x /\ B=metric_closed_ball x (h x)].
  have hbounded B:F B -> metric_set_bounded B.
    move=>[x [hx ->]]; exact (@covering_closed_ball_bounded R X x (h x) (ltW (hp x hx))).
  have [w hw]:=real_diameter_weight_exists hbounded.
  have hne B:F B -> B<>set0.
    move=>[x [hx ->]] he.
    have hh:metric_closed_ball x (h x) x by rewrite /metric_closed_ball /= mdistxx; exact: ltW (hp x hx).
    by rewrite he in hh.
  have hwn B (hB:F B):0<=w B:=diameter_weight_nonnegative hw hB.
  have hwb:exists C:R,forall B,F B -> w B<=C.
    exists (M+M)=>B [x [hx ->]].
    have hF:F (metric_closed_ball x (h x)) by exists x.
    apply: le_trans (diameter_weight_ball_bound hw hF (ltW (hp x hx))) _.
    exact: lerD (hM x hx) (hM x hx).
  have ht:(1:R)<2 by rewrite ltr1n.
  pose G:=weighted_cover_selection hne hwn hwb ht.
  have hG:is_weighted_cover_selection F w 2 G:=weighted_cover_selection_specification hne hwn hwb ht.
  have hGF:=weighted_selection_members hG.
  have hex B:exists x,F B -> U x /\ B=metric_closed_ball x (h x).
    case:(pselect (F B))=>[hB|hB].
    + have [x hx]:=hB; exists x=>_; exact hx.
    + exists x0=>hb; by exfalso; exact: hB hb.
  have [center hc]:=choice hex.
  pose S:=center @` G.
  have hSU:S `<=` U by move=>s [B hB <-]; exact (hc B (hGF B hB)).1.
  exists S; split=>//; split.
  + move=>s t [B hB <-] [C hC <-] hst.
    have hBC:B<>C by move=>he; apply: hst; by rewrite he.
    rewrite -(hc B (hGF B hB)).2 -(hc C (hGF C hC)).2.
    exact (weighted_selection_disjoint hG hB hC hBC).
  + move=>x hx.
    have hFx:F (metric_closed_ball x (h x)) by exists x.
    have [B [hB [hmeet hweight]]]:=weighted_selection_dominates hG hFx.
    have [hs hBs]:=hc B (hGF B hB).
    pose s:=center B.
    have hsS:S s by exists B.
    have hFs:F (metric_closed_ball s (h s)) by rewrite -hBs; exact: hGF.
    have hwx:=diameter_weight_euclidean_ball hw hFx (ltW (hp x hx)).
    have hws:=diameter_weight_euclidean_ball hw hFs (ltW (hp s hs)).
    rewrite hBs hwx hws in hweight.
    have hn:metric_closed_ball x (h x) `&` metric_closed_ball s (h s) != set0.
      apply/eqP; by rewrite -hBs.
    have [y [hxy hsy]]:=(set0P _).1 hn.
    have hdist:mdist s x<=h s+h x.
      apply: le_trans (metric_triangle s y x) _.
      apply: lerD hsy _; by rewrite metric_sym; exact hxy.
    exists s=>//; have hsp:=hp s hs.
    by apply: le_lt_trans hdist _; lra.
- exists set0; split; first by move=>x [].
  split; first by move=>s t [].
  move=>x hx; exfalso; apply: hempty; by exists x.
Qed.
