(** Federer (1969), 2.10.32, pp. 196–197: the sharp exterior-product upper
    bound for Lebesgue measure of an arbitrary nonempty Euclidean set. The
    compact convex inequality is already proved by Steiner symmetrisation.
    Pass to the closed convex hull, whose cost is unchanged by the existing
    universal-property and continuity laws, then use its abstract compact
    exhaustion. The original set need not be measurable or bounded. That
    outlook prints diam(S) twice where the corresponding comparison requires
    diam(S)^n; this file follows Federer's printed exterior-supremum formula
    and the proved product-norm bound. This reference-wording correction is
    distinct from Federer's own erratum. The normalising factor retains
    Federer's erratum p. 4, book p. 197 line 4. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric InnerConvex InnerConvexNeighbourhoods ConvexHull
  EuclideanLebesgueDimensions MeasureBasic ExteriorMeasureGauge ExteriorDiameter ExteriorDiameterClosure
  ExteriorDiameterConvexity HausdorffDiameterCost EuclideanBallVolume ClosedConvexExteriorVolumeBound.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [lebesgue_top_exterior_cost_bound]: direct
    inequality of 2.10.32, pp. 196–197,
    written using its proof's cost zeta from
    2.10.3. Closure and convex hull preserve
    this cost; measure monotonicity handles
    arbitrary, possibly nonmeasurable S. *)
Theorem lebesgue_top_exterior_cost_bound (R : realType) (n : nat)
    (S : set (inner_metric_space (@euclidean_inner_productP R n))) :
  S !=set0 -> (euclidean_lebesgue_measure n S<=exterior_diameter_cost n S)%E.
Proof.
move=> [a ha].
pose hB := @euclidean_inner_productP R n.
pose C : set (inner_metric_space hB) := @closure (inner_metric_space hB) (@convex_hull R (R_n R n) S).
have hSC : S `<=` C.
  move=> x hx; apply: subset_closure; exact (@convex_hull_includes R (R_n R n) S x hx).
have hne : C !=set0 by exists a; exact: hSC a ha.
have hclosed : closed C := @closed_closure (inner_metric_space hB) (@convex_hull R (R_n R n) S).
have hconv : is_inner_convex C := @inner_convex_closure R (R_n R n) (@euclidean_inner_product R n)
  hB (@convex_hull R (R_n R n) S) (@convex_hull_convex R (R_n R n) S).
have hcost : exterior_diameter_cost n C=exterior_diameter_cost n S.
  by rewrite /C exterior_diameter_cost_closure exterior_diameter_cost_convex_hull.
have hC := @closed_convex_lebesgue_exterior_bound R n C hne hclosed hconv.
rewrite hcost in hC.
exact (le_trans (measure_mono (euclidean_lebesgue_is_measure R n) hSC) hC).
Qed.

(** Source for [federer_2_10_32]: direct printed endpoint-
    supremum bound in 2.10.32, p. 196,
    with its proof completed on p. 197.
    The coefficient is alpha(n)/2^n and the
    abstract supremum is that of the actual
    n-fold endpoint-difference exterior norms.
    All natural dimensions are included; dimension
    zero uses the existing empty-product convention. *)
Theorem federer_2_10_32 (R : realType) (n : nat)
    (S : set (inner_metric_space (@euclidean_inner_productP R n))) :
  S !=set0 ->
  (euclidean_lebesgue_measure n S<=
    (euclidean_unit_ball_volume R n/(2 : R)^+n)%R%:E*extended_exterior_diameter n S)%E.
Proof. exact: lebesgue_top_exterior_cost_bound. Qed.
