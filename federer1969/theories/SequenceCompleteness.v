(** Federer (1969), 2.2.6, p. 63: the sequence metric space is complete. We
    prove completeness from eventual coordinate constancy for proper Cauchy
    filters and the abstract realisation of every coordinate sequence. No
    external product completeness theorem is used. Source context:
    SequenceSpaceUP.v. *)
From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals topology.
From Federer Require Import SequenceSpaceUP SequenceSpace SequenceCoordinates
  SequenceWeights SequenceMetricPrefixes SequenceProductTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

HB.instance Definition _ (R : realType) :=
  isPointed.Build (positive_sequence_space R) (positive_sequence_default R).

(** Source for [positive_sequence_cauchy_coordinate]: Federer 2.2.6, p. 63,
    supporting completeness argument: each coordinate is eventually constant
    along any proper Cauchy filter, since a small ball fixes that
    coordinate. *)
Lemma positive_sequence_cauchy_coordinate (R : realType)
    (F : set_system (positive_sequence_space R)) (PF : ProperFilter F) :
  cauchy F -> forall i, exists k,
    F [set x | positive_sequence_coordinates x i = k].
Proof.
move=> hF i; have he : 0 < @sequence_metric_weight R i / 2.
  by rewrite divr_gt0 ?sequence_metric_weight_positive ?ltr0n.
have [a ha] := proj1 (@cauchyP R _ F PF) hF _ he.
exists (positive_sequence_coordinates a i); apply: filterS ha=> x hx.
apply: esym; apply: (@positive_sequence_small_distance_coordinate R _ _ _
  (positive_sequence_distance_specification R) a x i).
by rewrite ballEmdist /= positive_sequence_metric_distanceE in hx.
Qed.

(** Source for [positive_sequence_cauchy_limit_exists]: Federer
    2.2.6, p. 63, direct completeness assertion. Choose each
    eventually constant coordinate and realise that sequence. Every
    finite initial-coordinate cylinder belongs to the filter, hence
    every metric neighborhood of the resulting point does. *)
Theorem positive_sequence_cauchy_limit_exists (R : realType)
    (F : set_system (positive_sequence_space R)) (PF : ProperFilter F) :
  cauchy F -> exists x : positive_sequence_space R, F --> x.
Proof.
move=> hF; have FF : Filter F := @filter_filter _ F PF.
have hc := @positive_sequence_cauchy_coordinate R F PF hF.
pose k i := projT1 (cid (hc i)).
have hk i : F [set x | positive_sequence_coordinates x i = k i].
  exact: projT2 (cid (hc i)).
pose x := @positive_sequence_from_coordinates R k.
have hx : positive_sequence_coordinates x = k := positive_sequence_coordinatesK k.
have hp N : F (positive_sequence_prefix x N).
  elim: N=> [|N IH].
  - have hT : F setT := @filterT _ F FF.
    apply: (@filterS _ F FF _ _ _ hT)=> y _ i; by rewrite ltn0.
  - apply: (@filterS _ F FF _ _ _ (@filterI _ F FF _ _ IH (hk N)))=> y [hy hN] i hi.
    case: (ltngtP i N)=> hiN.
    + exact: hy i hiN.
    + by move: hi; rewrite ltnS leqNgt hiN.
    + by rewrite hiN hx hN.
exists x=> U hu; have [N hN] := proj1 (positive_sequence_product_neighborhoods x U) hu.
exact: (@filterS _ F FF _ _ hN (hp N)).
Qed.

(** Source for [positive_sequence_complete]: Federer 2.2.6,
    p. 63, completeness in the general topological interface;
    this is the preceding proved limit existence, not a new axiom. *)
Lemma positive_sequence_complete (R : realType)
    (F : set_system (positive_sequence_space R)) (PF : ProperFilter F) :
  cauchy F -> cvg F.
Proof. move=> hF; apply/cvg_ex; exact: positive_sequence_cauchy_limit_exists PF hF. Qed.

HB.instance Definition _ (R : realType) :=
  Uniform_isComplete.Build (positive_sequence_space R) (@positive_sequence_complete R).
