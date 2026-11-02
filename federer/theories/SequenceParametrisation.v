(** Federer (1969), 2.2.8, pp. 64–65: every complete, separable, nonempty
    metric space is the image of the positive- integer sequence space under
    a locally Lipschitzian map. The public theorem combines sealed tree and
    branch-map witnesses with abstract surjectivity and regularity proofs.
    Source context and conventions: ClosedCoverTreeUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra
  classical_sets cardinality reals topology.
From Federer Require Import SequenceSpace CompleteMetricUP ClosedCoverTreeUP
  ClosedCoverTreeSealed ClosedCoverMapUP ClosedCoverMapSealed
  ClosedCoverSurjectivity ClosedCoverMapLipschitz ClosedCoverMapContinuous LipschitzUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [complete_separable_sequence_parametrisation]: direct
    formalisation of Federer 2.2.8, pp. 64–65, retaining completeness,
    separability and nonemptiness of X. The map is onto and locally
    Lipschitzian; continuity is exposed as a proved consequence for later
    descriptive-set-theory uses. *)
Theorem complete_separable_sequence_parametrisation (R : realType) (T : metricType R) :
  is_complete_metric_space T ->
  (exists D : set T, countable D /\ dense D) -> (@setT T) !=set0 ->
  exists g : positive_sequence_space R -> T,
    (forall x, exists n, g n = x) /\ is_locally_metric_lipschitz setT g /\ continuous g.
Proof.
move=> hT [D [hc hd]] hn.
pose E := @ClosedCoverTree.value R T D hc hd hn.
have hE : is_closed_cover_tree E := @ClosedCoverTree.laws R T D hc hd hn.
pose g := @ClosedCoverMap.value R T hT E hE.
have hg : is_closed_cover_map E g := @ClosedCoverMap.laws R T hT E hE.
exists g; split; first exact: (@closed_cover_map_surjective R T E hE g hg).
split; [exact: (@closed_cover_map_locally_lipschitz R T E hE g hg)|exact: (@closed_cover_map_continuous R T E hE g hg)].
Qed.
