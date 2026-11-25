(** Federer (1969), 2.8.19, p. 152: Vitali relations from refining Borel
    partitions. The public numbered theorem retains the printed hypotheses;
    supporting results expose the weaker hypotheses actually used. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets cardinality reals constructive_ereal topology.
From Federer Require Import MeasureUP MeasureBasic CoveringFamilyUP CountablyClosedFamilyUP
  CoveringRelationUP CoveringRelationFineness BorelPartition RefiningBorelPartitionsUP
  RefiningPartitionLaws PartitionMaximalCover MetricDiameter ExtendedRealBounds ExtendedRealOrderLimit.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [partition_relation_fine]: the everywhere
    fineness of V in Federer 2.8.19, p. 152,
    from the displayed uniform diameter limit. Only arbitrarily
    fine levels are needed in this supporting assertion. *)
Lemma partition_relation_fine (R : realType) (X : metricType R)
    (P : nat -> set (set X)) :
  is_refining_borel_partitions P ->
  (forall e : R, (0 < e)%R -> exists n, partition_level_diameter_sup P n < e%:E) ->
  forall x, covering_relation_fine_at (partition_covering_relation P) x.
Proof.
move=> hp hsmall x; apply: (covering_relation_fine_iff_small_diameter _ x).2=> e he.
have [n hn] := hsmall e he.
have [S [hS hxS]] := @partition_level_point_cell X P hp n x.
exists S; split.
- split=> //; by exists n.
- apply: le_lt_trans _ hn; apply: extended_real_sup_upper; by exists S.
Qed.

(** Source for [partition_relation_exact_selection]: the complete selection
    assertion in the proof of Federer 2.8.19, p. 152: coverage of Z suffices
    and the selected maximal members cover Z exactly. No measure or fineness
    premise is needed in this supporting result. *)
Theorem partition_relation_exact_selection (X : topologicalType)
    (P : nat -> set (set X)) (C : X -> set X -> Prop) (Z : set X) :
  is_refining_borel_partitions P ->
  (forall x S, C x S -> partition_covering_relation P x S) ->
  Z `<=` \bigcup_(S in covering_relation_image C Z) S ->
  exists G : set (set X), G `<=` covering_relation_image C Z /\
    countable G /\ set_family_disjoint G /\ Z `<=` \bigcup_(S in G) S.
Proof.
move=> hp hC hcover.
have hF : covering_relation_image C Z `<=` partition_levels_family P.
  move=> S [x [_ hx]]; exact: (hC x S hx).2.
have [G [hG [hc [hd he]]]] := @partition_maximal_subfamily_cover X P
  (covering_relation_image C Z) hp hF.
exists G; split=> //; split=> //; split=> //; by rewrite he.
Qed.

(** Source for [refining_partitions_vitali]: supporting form of Federer
    2.8.19, p. 152 A measure and arbitrarily fine refining Borel partition
    levels suffice. The selection argument has no exceptional remainder, so
    no measure regularity, boundedness or ambient separability is used. *)
Theorem refining_partitions_vitali (R : realType) (X : metricType R)
    (phi : set X -> \bar R) (P : nat -> set (set X)) :
  is_measure phi -> is_refining_borel_partitions P ->
  (forall e : R, (0 < e)%R -> exists n, partition_level_diameter_sup P n < e%:E) ->
  is_vitali_relation phi (partition_covering_relation P).
Proof.
move=> hm hp hsmall.
constructor.
- by move=> x S [].
- move=> S [x [_ [_ [n _ hn]]]].
  exact (@borel_partition_members X setT (P n) (refining_partition_levels hp n) S hn).
- exact: partition_relation_fine hp hsmall.
- move=> C Z hCV hf.
  have hcover : Z `<=` \bigcup_(S in covering_relation_image C Z) S.
    move=> x hx.
    have [S [hS _]] := (covering_relation_fine_iff_small_diameter C x).1 (hf x hx) 1%R (@ltr01 R).
    exists S; last exact: (hCV x S hS).1.
    by exists x.
  have [G [hG [hc [hd hZ]]]] := @partition_relation_exact_selection X P C Z hp hCV hcover.
  exists G; split=> //; split=> //; split=> //.
  have he : (Z `\` \bigcup_(S in G) S) = set0.
    apply/seteqP; split=> [x [hx hn]|x []]; exfalso; exact: hn (hZ x hx).
  by rewrite he (measure_empty hm).
Qed.

(** Source for [federer_2_8_19]: direct formalisation of the
    complete theorem in Federer 2.8.19, p. 152,
    retaining separability, bounded first-level cells, the exact
    order limit zero of the diameter suprema, and the standing
    measure hypotheses of 2.8.1, p. 141. The proof
    delegates to the stronger supporting result; its exact
    selection follows the book's maximal-member proof. *)
Theorem federer_2_8_19 (R : realType) (X : metricType R)
    (phi : set X -> \bar R) (P : nat -> set (set X)) :
  is_measure phi ->
  (forall W, open W -> measure_measurable phi W) ->
  (forall A, metric_set_bounded A -> phi A < +oo) ->
  (exists D : set X, countable D /\ dense D) ->
  is_refining_borel_partitions P ->
  (forall S, P 0%N S -> metric_set_bounded S) ->
  extended_order_limit (partition_level_diameter_sup P) 0 ->
  is_vitali_relation phi (partition_covering_relation P).
Proof.
move=> hm _ _ _ hp _ hlim.
apply: refining_partitions_vitali hm hp _=> e he.
have heE : (0 < e%:E)%E by rewrite lte_fin.
have [N hN] := hlim.2 e%:E heE.
exists N; exact: hN N (leqnn N).
Qed.
