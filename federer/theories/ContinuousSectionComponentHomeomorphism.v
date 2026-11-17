(** Federer (1969), 3.4.8(10), p. 332:
    the original projection maps each sheet
    component homeomorphically onto its base
    component. Both maps use the actual
    metric subspace topologies and the proved
    continuous section and component identities. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals topology.
From Federer Require Import MetricSubsetBackground MetricSubsetCorestriction HomeomorphismUP
  ContinuousSectionComponents.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [continuous_section_component_homeomorphism]:
    the component homeomorphism in 3.4.8(10),
    p. 332, for one original
    continuous ordered sheet. Its forward
    map is the supplied projection; the
    supplied inverse section gives the inverse.
    No bijection or homeomorphism is assumed. *)
Theorem continuous_section_component_homeomorphism (R:realType) (X Y:metricType R)
    (P:X->Y) (V:set Y) (psi:Y->X) (a:Y):
  continuous P ->(forall y,V y ->{for y,continuous psi}) ->
  (forall y,V y ->P (psi y) = y) ->V a ->
  exists F:metric_subset (connected_component (psi @` V) (psi a))->
      metric_subset (connected_component V a),
    (forall x,val (F x) = P (val x)) /\is_homeomorphism F.
Proof.
move=>hP hPsi hCancel ha.
pose CX:=connected_component (psi @` V) (psi a).
pose CY:=connected_component V a.
have [hImage hProjection]:=@continuous_section_component_image X Y P V psi hP hPsi hCancel a ha.
have hCY:CY `<=` V:=@connected_component_sub Y V a.
have hCX:CX `<=` (psi @` V):=@connected_component_sub X (psi @` V) (psi a).
have hInverse x:(psi @` V) x ->psi (P x) = x.
  by move=>[y hy <-];rewrite hCancel.
have hForward (x:metric_subset CX):CY (P (val x)).
  change ((connected_component V a) (P (val x))).
  rewrite -hProjection;exists (val x);first exact:set_valP x.
  by [].
have hBackward (y:metric_subset CY):CX (psi (val y)).
  change ((connected_component (psi @` V) (psi a)) (psi (val y))).
  rewrite hImage;exists (val y);first exact:set_valP y.
  by [].
pose F:metric_subset CX->metric_subset CY:=@metric_subset_corestriction R Y
  (metric_subset CX) CY (fun x=>P (val x)) hForward.
pose G:metric_subset CY->metric_subset CX:=@metric_subset_corestriction R X
  (metric_subset CY) CX (fun y=>psi (val y)) hBackward.
have hFContinuous:continuous F.
  apply:metric_subset_corestriction_continuous.
  move=>x W hW.
  exact:(@metric_subset_inclusion_continuous R X CX x _ (hP (val x) W hW)).
have hGContinuous:continuous G.
  apply:metric_subset_corestriction_continuous.
  move=>y W hW.
  have hAt:=hPsi (val y) (hCY (val y) (set_valP y)).
  exact:(@metric_subset_inclusion_continuous R Y CY y _ (hAt W hW)).
exists F;split;first by move=>x.
exists G;constructor;[exact:hFContinuous|exact:hGContinuous| |].
- move=>x;apply:val_inj;change (psi (P (val x)) = val x).
  exact:hInverse (val x) (hCX (val x) (set_valP x)).
- move=>y;apply:val_inj;change (P (psi (val y)) = val y).
  exact:hCancel (val y) (hCY (val y) (set_valP y)).
Qed.
