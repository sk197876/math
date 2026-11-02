(** General topology supporting the open-cover assertion of Federer (1969),
    2.10.3, p. 172. An open neighbourhood of a compact finite Cartesian
    power contains the same power of a sufficiently small metric
    neighbourhood of the original compact set. Use the finite-subcover
    principle of 2.2.5, p. 63, with common-radius coordinate boxes. This is
    a supporting proof ingredient, not an extra numbered claim attributed to
    Federer. Source context and finite-product continuity context:
    ExteriorEndpointContinuity.v. *)
From mathcomp Require Import all_boot all_order all_algebra finmap boolp classical_sets
  cardinality reals topology.
From mathcomp Require Import lra.
From Federer Require Import MetricCoordinateBoxes MetricOpenThickening CompactFiniteCover
  FiniteOffTargetBallCover.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory ArrowAsProduct.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [compact_finite_power_neighbourhood]: supporting
    uniform endpoint enlargement for Federer 2.10.3,
    p. 172. The conclusion allows empty compact sets
    and empty finite coordinate domains; no chosen point
    in the compact set is assumed. *)
Theorem compact_finite_power_neighbourhood (R : realType) (I : finType) (X : metricType R)
    (A : set X) (U : set (I -> X)) : compact A -> open U ->
  (forall p, (forall i, A (p i)) -> U p) ->
  exists r : R, 0<r /\ forall q : I -> X,
    (forall i, metric_open_thickening A r (q i)) -> U q.
Proof.
move=> hA hU hAU.
pose K : set (I -> X) := [set p | forall i, A (p i)].
have hK : compact K := @tychonoff I (fun _ => X) (fun _ => A) (fun _ => hA).
pose J := [the choiceType of ((I -> X)*R)%type].
pose D : set J := [set z | K z.1 /\ 0<z.2 /\ metric_coordinate_box z.1 z.2 `<=` U].
pose V (z : J) := metric_coordinate_box z.1 (z.2/2).
have hcover : K `<=` \bigcup_(z in D) V z.
  move=> p hp.
  have hn : nbhs p U by have ho := hU; rewrite openE in ho; exact: ho p (hAU p hp).
  have [r [hr hsub]] := product_neighbourhood_coordinate_box hn.
  exists (p,r); first by split=> //; split.
  apply: metric_coordinate_box_self; by rewrite divr_gt0 // ltr0n.
have ho z : D z -> open (V z) by move=> _; exact: finite_metric_coordinate_box_open.
have [F hF hcov] := @compact_open_finite_cover [the topologicalType of (I -> X)] J D V K hK ho hcover.
have hpos z : [set` F] z -> 0<z.2/2.
  move=> hz; have hDz : D z := set_mem (hF z hz).
  by rewrite divr_gt0 //; exact: hDz.2.1.
have [r [hr hrlow]] := @finite_positive_values_lower_bound R J [set` F]
  (fun z => z.2/2) (finite_fset F) hpos.
exists r; split=> // q hq.
have hex i : exists a : X, A a /\ mdist a (q i)<r.
  have [a ha hd] := hq i; exists a; by split.
pose p i := projT1 (cid (hex i)).
have hp i : A (p i) /\ mdist (p i) (q i)<r := projT2 (cid (hex i)).
have hPK : K p by move=> i; exact: (hp i).1.
have [z hz hpz] := hcov p hPK.
have hDz : D z := set_mem (hF z hz).
have hpq : metric_coordinate_box p r q by move=> i; exact: (hp i).2.
have hbox := metric_coordinate_box_triangle hpz hpq.
apply: hDz.2.2.
apply: (@metric_coordinate_box_mono R I X z.1 (z.2/2+r) z.2 _ q hbox).
have hh := hrlow z hz; lra.
Qed.
