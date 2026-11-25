(** Federer (1969), 2.2.17, p. 72: proper continuous images of Radon
    measures. This proves a stronger whole-domain result without a countable
    compact cover; the final Federer theorem below retains that printed
    hypothesis. that extension is not claimed here. Source context and the
    documented proof variant: ProperMapUP.v and ProperOuterNeighborhood.v. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets
  reals constructive_ereal topology.
From Federer Require Import MeasureUP MeasureBasic MeasurePushforward RadonMeasureUP
  ProperMapUP ProperContinuousClosed ProperOuterNeighborhood PushforwardMeasurableSets.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [proper_continuous_radon_pushforward]: supporting stronger
    form of Federer 2.2.17, p. 72. Compact finiteness, open measurability
    and inner regularity pass through inverse images and compact images. The
    closed map supplies the open neighborhoods for outer regularity. *)
Theorem proper_continuous_radon_pushforward (R : realType)
    (X Y : topologicalType) (mu : set X -> \bar R) (hm : is_measure mu)
    (hr : is_radon_measure mu) (f : X -> Y) :
  hausdorff_space Y -> locally_compact (@setT Y) -> continuous f -> is_proper_map f ->
  is_radon_measure (measure_pushforward f mu).
Proof.
move=> hY hl hf hp.
have hclosed := @proper_continuous_map_closed X Y f hY hl hf hp.
have hpre V : open V -> open (f @^-1` V) := (proj1 (continuousP f)) hf V.
constructor=> //.
- move=> K hK; exact: (@radon_compact_finite R X mu hr _ (hp K hK)).
- move=> V hV; apply: pushforward_measurable_from_preimage.
  exact: (@radon_open_measurable R X mu hr _ (hpre V hV)).
- move=> V hV c hc; apply: (@radon_inner_least R X mu hr _ (hpre V hV) c).
  move=> K hK hKV.
  have hKi : compact (f @` K).
    apply: continuous_compact _ hK; exact: continuous_subspaceT hf.
  have hVi : f @` K `<=` V by move=> y [x hx <-]; exact: hKV x hx.
  apply: le_trans _ (hc (f @` K) hKi hVi).
  apply: (@measure_mono R X mu hm K (f @^-1` (f @` K)))=> x hx; by exists x.
- move=> B c hc; apply: (@radon_outer_greatest R X mu hr (f @^-1` B) c)=> U hU hBU.
  have [W [hW [hBW hWU]]] := @proper_outer_open_neighborhood X Y f B U hclosed hU hBU.
  apply: le_trans (hc W hW hBW) _.
  exact: (@measure_mono R X mu hm (f @^-1` W) U hWU).
Qed.

(** Source for [federer_2_2_17_radon_pushforward]: direct statement of
    Federer 2.2.17, p. 72. The source locally compact Hausdorff hypotheses
    are carried by the Radon specification; its countable compact-cover
    hypothesis is retained although. *)
Theorem federer_2_2_17_radon_pushforward (R : realType)
    (X Y : topologicalType) (mu : set X -> \bar R) (hm : is_measure mu)
    (hr : is_radon_measure mu) (f : X -> Y) :
  hausdorff_space Y -> locally_compact (@setT Y) -> has_countable_compact_cover X ->
  continuous f -> is_proper_map f ->
  is_measure (measure_pushforward f mu) /\ is_radon_measure (measure_pushforward f mu).
Proof.
move=> hY hl hcover hf hp; split.
- exact: measure_pushforward_is_measure hm.
- exact: (@proper_continuous_radon_pushforward R X Y mu hm hr f hY hl hf hp).
Qed.
