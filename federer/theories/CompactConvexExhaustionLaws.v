(** Consequences of the abstract compact exhaustion for Federer (1969),
    2.10.32, pp. 196–197. The compact convex volume inequality passes to the
    target through 2.1.3(4), p. 55. All compact pieces are Borel measurable;
    the limiting volume and cost may be infinite. No particular exhaustion
    construction, centre or choice of radii is used. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import InnerProductUP InnerMetric InnerConvex CompactSetDistanceProfile
  CompactConvexExhaustionUP EuclideanInnerProduct EuclideanLebesgueDimensions MeasureUP
  MeasureContinuityBelow ExtendedRealOrderLimit TopologicalBorel BorelRegularMeasureUP
  ExteriorMeasureGauge CompactConvexExteriorVolumeBound.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [compact_convex_exhaustion_union]: supporting
    exact union equality for the compact reduction
    of 2.10.32, pp. 196–197, derived only
    from containment and covering laws. *)
Lemma compact_convex_exhaustion_union (R : realType) (V : lmodType R)
    (B : V -> V -> R) (hB : is_inner_product B) (C : set (inner_metric_space hB))
    (A : nat -> compact_metric_set (inner_metric_space hB)) :
  is_compact_convex_exhaustion hB C A -> \bigcup_k val (A k)=C.
Proof.
move=> hA.
have hsub : forall k, val (A k) `<=` C := compact_convex_exhaustion_subset_law hA.
apply/seteqP; split; last exact: compact_convex_exhaustion_cover_law hA.
move=> x [k _ hx]; exact (hsub k x hx).
Qed.

(** Source for [exhaustion_lebesgue_exterior_bound]: supporting
    passage from compact convex pieces to their
    union for the arbitrary-set assertion in
    2.10.32, pp. 196–197. Uses exactly the
    increasing measurable-set continuity of 2.1.3(4),
    p. 55, without a finite limiting measure
    or finite exterior-cost assumption. *)
Theorem exhaustion_lebesgue_exterior_bound (R : realType) (n : nat)
    (C : set (inner_metric_space (@euclidean_inner_productP R n)))
    (A : nat -> compact_metric_set (inner_metric_space (@euclidean_inner_productP R n))) :
  is_compact_convex_exhaustion (@euclidean_inner_productP R n) C A ->
  (euclidean_lebesgue_measure n C<=exterior_diameter_cost n C)%E.
Proof.
move=> hA.
have hconv : forall k, is_inner_convex (val (A k)) := compact_convex_exhaustion_convex_law hA.
have hsub : forall k, val (A k) `<=` C := compact_convex_exhaustion_subset_law hA.
have hmono : forall k l, (k<=l)%N -> val (A k) `<=` val (A l) :=
  compact_convex_exhaustion_increasing_law hA.
have hm := euclidean_lebesgue_is_measure R n.
have hr := euclidean_lebesgue_borel_regular R n.
have hmeas k : measure_measurable (@euclidean_lebesgue_measure R n) (val (A k)).
  apply: (borel_regular_borel_measurable hm hr); apply: closed_borel_set.
  exact (compact_closed (@metric_hausdorff R (inner_metric_space (@euclidean_inner_productP R n))) (set_valP (A k)).1).
have hpoint k : (euclidean_lebesgue_measure n (val (A k))<=exterior_diameter_cost n C)%E.
  exact (le_trans (@compact_convex_lebesgue_exterior_bound R n (A k) (hconv k))
    (@exterior_diameter_cost_mono R n n (val (A k)) C (hsub k))).
have hlim := @measure_continuity_below R (inner_metric_space (@euclidean_inner_productP R n))
  (@euclidean_lebesgue_measure R n) hm (fun k=>val (A k)) hmeas hmono.
rewrite (compact_convex_exhaustion_union hA) in hlim.
rewrite leNgt; apply/negP=> hbad.
have [N hN] := hlim.2.1 _ hbad.
have hh := lt_le_trans (hN N (leqnn N)) (hpoint N).
by rewrite ltxx in hh.
Qed.
