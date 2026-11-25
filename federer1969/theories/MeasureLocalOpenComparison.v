(** Federer (1969), 3.2.46, pp. 281–282: local
    measure comparisons globalise by a countable Borel
    partition. This expands the printed localisation step.
    Original test subsets need not be measurable or finite. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp
  classical_sets cardinality constructive_ereal topology.
From Federer Require Import CountableOpenBaseUP CountableBaseLindelof
  TopologicalBorel BorelPartition BorelSubordinatePartition
  MeasureUP MeasureBasic MeasureRestriction DisjointAlmostCoverComparison.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [measure_local_open_comparison]: local
    inequalities on every subset of an open neighbourhood
    imply the same global comparison, supporting 3.2.46,
    pp. 281–282. Restrict both measures by the arbitrary
    original test set before using the Borel partition;
    no measurability of that test set is assumed. *)
Theorem measure_local_open_comparison (R : realType) (X : topologicalType)
    (mu nu : set X -> \bar R) (U : nat -> set X) (t : R) :
  is_measure mu -> is_measure nu -> is_countable_open_base U -> 0<=t ->
  (forall B, borel_set B -> measure_measurable mu B /\ measure_measurable nu B) ->
  (forall x, exists V : set X, open V /\ V x /\
    forall S, S `<=` V -> (mu S<=t%:E*nu S)%E) ->
  forall S, (mu S<=t%:E*nu S)%E.
Proof.
move=> hMu hNu hBase ht hBorel hLocal S.
pose C := [set V : set X | open V /\ forall B, B `<=` V -> (mu B<=t%:E*nu B)%E].
have hOpen V : C V -> open V by move=> [hV _].
have hCover : setT `<=` \bigcup_(V in C) V.
  move=> x _; have [V [hV [hx hBound]]] := hLocal x.
  exists V; last exact hx; by split.
have [G [hGC [hCount hGCover]]] := countable_base_open_subcover hBase hOpen hCover.
have hGBorel V (hV : G V) : borel_set V := open_borel_set (hOpen V (hGC V hV)).
have [H [hH hSub]] := borel_countable_cover_subordinate_partition
  (open_borel_set (@openT X)) hCount hGBorel hGCover.
pose mS := measure_restrict mu S.
pose nS := measure_restrict nu S.
have hMS := measure_restrict_is_measure hMu S.
have hNS := measure_restrict_is_measure hNu S.
have hMeas B (hB : H B) : measure_measurable mS B /\ measure_measurable nS B.
  have hBoth := hBorel B (borel_partition_members hH hB).
  split.
  - exact (@measure_restrict_measurable R X mu S B hBoth.1).
  - exact (@measure_restrict_measurable R X nu S B hBoth.2).
have hDisjoint B D (hB : H B) (hD : H D) (hBD : B<>D) : B `&` D=set0.
  exact (@borel_partition_disjoint X setT H hH B D hB hD hBD).
have hNull : mS (setT `\` \bigcup_(B in H) B)=0%E.
  rewrite (borel_partition_union hH) setDv; exact: measure_empty.
have hBound B (hB : H B) : (mS B<=t%:E*nS B)%E.
  have [_ [V [hVG hBV]]] := hSub B hB.
  apply: (hGC V hVG).2=> x [_ hx]; exact: hBV x hx.
have h := @measure_disjoint_almost_cover_comparison R X [the choiceType of set X]
  mS nS setT H (fun B=>B) t hMS hNS ht
  (borel_partition_countable hH) (fun _ _ _ _=>Logic.I)
  (fun B hB=>(hMeas B hB).1) (fun B hB=>(hMeas B hB).2)
  hDisjoint hNull hBound.
by rewrite /mS /nS /measure_restrict !setIT in h.
Qed.
