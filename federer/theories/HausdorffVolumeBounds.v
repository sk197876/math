(** Closed volume lower bound on the compact-set class in Federer (1969),
    2.10.32, p. 196. Euclidean compact outer approximation gives an open
    cover whose volume is below a prescribed strict upper bound. All
    sufficiently close compact sets remain in that cover by the existing
    Hausdorff metric laws. Thus strict volume sublevels are open and volume
    lower-bound classes are closed. No continuity of volume under arbitrary
    Hausdorff limits is asserted. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import EuclideanInnerProduct InnerMetric CompactSetDistanceProfile CompactHausdorffMetric
  EuclideanCompactOpenVolume EuclideanLebesgueDimensions MeasureBasic HausdorffOpenContainment.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [hausdorff_euclidean_volume_strict_sublevel_open]:
    supporting upper semicontinuity used for the
    closedness claim in 2.10.32, p. 196.
    The open-cover comparison uses actual Lebesgue
    measure, not an independently postulated volume. *)
Theorem hausdorff_euclidean_volume_strict_sublevel_open (R : realType) (n : nat) (b : R) :
  open [set K : compact_hausdorff_space (inner_metric_space (@euclidean_inner_productP R n)) |
    (euclidean_lebesgue_measure n (val K)<b%:E)%E].
Proof.
rewrite openE=> K hK.
have [W [hW [hKW hvol]]] := @euclidean_compact_open_volume_bound R n (val K) b (set_valP K).1 hK.
have ho := hausdorff_compact_containment_open hW; rewrite openE in ho.
have hn := ho K hKW.
apply: (@filterS _ (nbhs K) _ _ _ _ hn)=> D hD.
exact (le_lt_trans (measure_mono (euclidean_lebesgue_is_measure R n) hD) hvol).
Qed.

(** Source for [hausdorff_euclidean_volume_superlevel_closed]: direct
    closedness of the volume lower-bound condition
    defining C in 2.10.32, p. 196. The
    threshold can be any real number; the printed
    application takes it positive. *)
Theorem hausdorff_euclidean_volume_superlevel_closed (R : realType) (n : nat) (a : R) :
  closed [set K : compact_hausdorff_space (inner_metric_space (@euclidean_inner_productP R n)) |
    (a%:E<=euclidean_lebesgue_measure n (val K))%E].
Proof.
have ho := @hausdorff_euclidean_volume_strict_sublevel_open R n a.
have he : [set K : compact_hausdorff_space (inner_metric_space (@euclidean_inner_productP R n)) |
      (a%:E<=euclidean_lebesgue_measure n (val K))%E]=
    ~` [set K : compact_hausdorff_space (inner_metric_space (@euclidean_inner_productP R n)) |
      (euclidean_lebesgue_measure n (val K)<a%:E)%E].
  apply/seteqP; split=> K hK.
  - move=> hbad; have hh := lt_le_trans hbad hK; by rewrite ltxx in hh.
  - change (is_true ((a%:E<=euclidean_lebesgue_measure n (val K))%E)).
    rewrite leNgt; apply/negP; exact hK.
rewrite he; exact: open_closedC ho.
Qed.
