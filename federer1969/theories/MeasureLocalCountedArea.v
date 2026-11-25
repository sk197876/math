(** Federer (1969), 3.2.46, p. 282: the area
    identity localises to countably many original source
    charts. This supporting measure lemma proves the
    countable assembly without assuming finite multiplicity,
    disjoint image patches or finite total measure. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp
  classical_sets cardinality constructive_ereal topology.
From Federer Require Import CountableOpenBaseUP CountableBaseLindelof
  TopologicalBorel BorelPartition BorelSubordinatePartition
  PartialFunctionUP PartialFunctionBasic MappingMultiplicity PartitionCountedAreaIntegral
  MeasureUP MeasureBasic MeasureFiniteClosure MeasureRestriction MeasureCountableAdditivity
  MeasureIntegralUP NonnegativeSum ExtendedRealOrderTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [measure_local_counted_area]: local
    proved area formulas on every measurable source subset
    give the formula for the original whole subset,
    supporting 3.2.46, p. 282. The geometric application
    must prove the local formula separately; no mathematical
    object is defined by the desired global identity. *)
Theorem measure_local_counted_area (R : realType) (X : topologicalType) (Y : choiceType)
    (mu nu : set X -> \bar R) (beta : set Y -> \bar R)
    (f : X -> Y) (U : nat -> set X) :
  is_measure mu -> is_measure nu -> is_measure beta -> is_countable_open_base U ->
  (forall B, borel_set B -> measure_measurable mu B /\ measure_measurable nu B) ->
  (forall x, exists V : set X, open V /\ V x /\ forall S,
    measure_measurable mu S -> S `<=` V ->
    is_measure_integral beta (partial_function_total
      (fun y=>(@mapping_multiplicity R X Y f S y : extended_real_line R))) (nu S)) ->
  forall S, measure_measurable mu S ->
  is_measure_integral beta (partial_function_total
    (fun y=>(@mapping_multiplicity R X Y f S y : extended_real_line R))) (nu S).
Proof.
move=> hMu hNu hBeta hBase hBorel hLocal S hS.
pose C := [set V : set X | open V /\ forall T, measure_measurable mu T -> T `<=` V ->
  is_measure_integral beta (partial_function_total
    (fun y=>(@mapping_multiplicity R X Y f T y : extended_real_line R))) (nu T)].
have hOpen V : C V -> open V by move=> [hV _].
have hCover : setT `<=` \bigcup_(V in C) V.
  move=> x _; have [V [hV [hx hFormula]]] := hLocal x.
  exists V; last exact hx; by split.
have [G [hGC [hCount hGCover]]] := countable_base_open_subcover hBase hOpen hCover.
have hGBorel V (hV : G V) : borel_set V := open_borel_set (hOpen V (hGC V hV)).
have [H [hH hSub]] := borel_countable_cover_subordinate_partition
  (open_borel_set (@openT X)) hCount hGBorel hGCover.
pose E B := S `&` B.
have hECover : S=\bigcup_(B in H) E B.
  apply/seteqP; split=> x.
  - move=> hx; have hAll : (\bigcup_(B in H) B) x by rewrite (borel_partition_union hH).
    have [B hB hxB] := hAll; exists B; first exact hB; by split.
  - by move=> [B hB [hx _]].
have hDisjoint B D (hB : H B) (hD : H D) (hBD : B!=D) x : E B x -> E D x -> False.
  move=> [_ hx] [_ hy].
  have hNot : B<>D by move=> hEq; by rewrite hEq eqxx in hBD.
  have hEmpty := @borel_partition_disjoint X setT H hH B D hB hD hNot.
  have hIn : (B `&` D) x by split.
  by rewrite hEmpty in hIn.
have hSum : nu S=nonnegative_sum H (fun B=>nu (E B)).
  have hRestrictedSum : measure_restrict nu S setT=
      nonnegative_sum H (fun B=>measure_restrict nu S B).
    rewrite -(borel_partition_union hH).
    apply: (@measure_countable_disjoint_additivity R X [the choiceType of set X]
      (measure_restrict nu S) (measure_restrict_is_measure hNu S) H (fun B=>B)
      (borel_partition_countable hH)).
    - move=> B hB; exact (@measure_restrict_measurable R X nu S B
        (hBorel B (borel_partition_members hH hB)).2).
    - move=> B D hB hD hBD x hx hy.
      have hNot : B<>D by move=> hEq; by rewrite hEq eqxx in hBD.
      have hEmpty := @borel_partition_disjoint X setT H hH B D hB hD hNot.
      have hIn : (B `&` D) x by split.
      by rewrite hEmpty in hIn.
  by rewrite /measure_restrict setIT in hRestrictedSum.
rewrite hSum.
apply: (@partition_counted_area_integral R X Y [the choiceType of set X] f S H E beta
  (fun B=>nu (E B)) hBeta (borel_partition_countable hH) hECover hDisjoint).
move=> B hB.
have [_ [V [hVG hBV]]] := hSub B hB.
apply: (hGC V hVG).2.
- exact (@measure_measurable_intersection R X mu hMu S B hS
    (hBorel B (borel_partition_members hH hB)).1).
- by move=> x [_ hx]; exact: hBV x hx.
Qed.
