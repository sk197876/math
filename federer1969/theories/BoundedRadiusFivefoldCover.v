(** Federer (1969), 3.1.13, p. 224:
    apply 2.8.4–2.8.5 with diameter weight
    and tau=2 to the positive radius balls.
    The diameter enlargement estimate gives
    the fivefold cover. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology lra.
From Federer Require Import MetricClosedBalls CoveringFamilyUP CoveringFamilyLaws
  CountablyClosedFamilyUP DiametricRegularityUP DiameterWeightLaws
  WeightedCoverSelectionUP WeightedCoverSelection WeightedEnlargements BallEnlargementBound.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [bounded_radius_disjoint_fivefold_cover]:
    the disjoint balls and fivefold cover
    selected in Federer 3.1.13, p. 224.
    The proof follows the cited weighted
    selection 2.8.4–2.8.5, pp. 143–144.
    The metric version requires only bounded
    positive radii; empty targets are included,
    and no unique center representation is assumed. *)
Theorem bounded_radius_disjoint_fivefold_cover (R : realType) (X : metricType R)
    (U : set X) (h : X->R) :
  (forall x, U x -> 0<h x) ->
  (exists M : R, forall x, U x -> h x<=M) ->
  exists S : set X,
    S `<=` U /\
    (forall s t, S s -> S t -> s<>t ->
      metric_closed_ball s (h s) `&` metric_closed_ball t (h t)=set0) /\
    U `<=` \bigcup_(s in S) metric_closed_ball s (5*h s).
Proof.
move=>hp [M hM].
case: (pselect (exists x, U x))=>[[x0 hx0]|hempty].
- pose F := [set B : set X | exists x, U x /\ B=metric_closed_ball x (h x)].
  have hbounded B : F B -> metric_set_bounded B.
    move=>[x [hx ->]]; exact: (covering_closed_ball_bounded x (ltW (hp x hx))).
  have [w hw] := real_diameter_weight_exists hbounded.
  have hnonempty B : F B -> B<>set0.
    move=>[x [hx ->]] he.
    have hm : metric_closed_ball x (h x) x.
      by rewrite /metric_closed_ball /= mdistxx; exact: (ltW (hp x hx)).
    by rewrite he in hm.
  have hwn B : F B -> 0<=w B := fun hB=>diameter_weight_nonnegative hw hB.
  have hwb : exists C : R, forall B, F B -> w B<=C.
    exists (M+M)=>B hB; have [x [hx he]] := hB.
    have hFb : F (metric_closed_ball x (h x)) by rewrite -he.
    rewrite he; apply: (le_trans (diameter_weight_ball_bound hw hFb (ltW (hp x hx)))).
    exact: (lerD (hM x hx) (hM x hx)).
  have ht : (1:R)<2 by rewrite ltr1n.
  pose G := weighted_cover_selection hnonempty hwn hwb ht.
  have hG : is_weighted_cover_selection F w 2 G :=
    weighted_cover_selection_specification hnonempty hwn hwb ht.
  have hGF : G `<=` F := weighted_selection_members hG.
  have hex B : exists x, F B -> U x /\ B=metric_closed_ball x (h x).
    case: (pselect (F B))=>[hB|hn].
    + have [x hx] := hB; by exists x.
    + exists x0; by move=>/hn.
  have [center hc] := choice hex.
  pose S := center @` G.
  have hSU : S `<=` U.
    move=>s [B hB <-]; exact: (hc B (hGF B hB)).1.
  exists S; split; first exact hSU.
  split.
  + move=>s t [B hB <-] [C hC <-] hne.
    have hBC : B<>C by move=>he; apply: hne; by rewrite he.
    rewrite -(hc B (hGF B hB)).2 -(hc C (hGF C hC)).2.
    exact: (weighted_selection_disjoint hG hB hC hBC).
  + move=>x hx.
    have hBx : F (metric_closed_ball x (h x)) by exists x.
    have hmember : metric_closed_ball x (h x) x.
      by rewrite /metric_closed_ball /= mdistxx; exact: (ltW (hp x hx)).
    have hcover := weighted_selection_enlargement_cover hG.
    have hballunion : (\bigcup_(B in F) B) x by exists (metric_closed_ball x (h x)).
    have [B hB hhat] := hcover x hballunion.
    exists (center B); first by exists B.
    have [hcenter he] := hc B (hGF B hB).
    have hFB : F (metric_closed_ball (center B) (h (center B))).
      by rewrite -he; exact: (hGF B hB).
    have htwo : (0:R)<=2 by rewrite ler0n.
    have hinc := diameter_enlargement_ball_bound hw htwo hFB (ltW (hp _ hcenter)).
    have halg : (1+2*2)*h (center B)=5*h (center B) by lra.
    rewrite halg in hinc.
    apply: hinc; by rewrite -he.
- exists set0; split; first by move=>x [].
  split; first by move=>s t [].
  move=>x hx; exfalso; apply: hempty; by exists x.
Qed.
