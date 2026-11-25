(** The scalar-coordinate Bohr counterexample supporting Federer
    (1969), 2.8.20, p. 152. The small-budget,
    small-rectangle measures are summed over countably many scales,
    following the nonnegative summation step in Cesari1939,
    section II.4, p. 307. All exceptional remainders are
    removed from the unit square, leaving area one. A disjoint
    almost cover by the large-mass cells would require mass at
    least two from a measure of total mass at most one.
    The final Euclidean formulation is separate. Source titles
    and proof-route comparison: VitaliMassObstruction.v and
    SmallRectangleMassCover.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  cardinality reals constructive_ereal topology.
From Federer Require Import ScalarPlaneRectangles ScalarMetricPlane SmallRectangleMassCoverUP
  SmallRectangleMassCover MeasureUP MeasureBasic MeasureAlmostBasic MeasureSum
  NonnegativeSum DyadicDensityWeights ArchimedeanReciprocal MetricDiameter
  CoveringRelationUP CoveringRelationFineness VitaliMassObstruction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [scalar_rectangle_relation]: coordinate form
    of the relation {(x,S): x in S in F} in Federer
    2.8.20, p. 152. F consists of products of
    compact nondegenerate scalar intervals. *)
Definition scalar_rectangle_relation (R : realType) (x : scalar_metric_plane R)
    (S : set (scalar_metric_plane R)) := S x /\ is_nondegenerate_scalar_rectangle S.

(** Source for [scalar_rectangle_mass_obstruction_exists]: supporting
    summed-measure witness for the counterexample in Federer
    2.8.20, p. 152; Cesari1939 section II.4,
    p. 307. A target of area one has arbitrarily
    small eligible rectangles through each point, each carrying
    at least twice its area in a measure of total mass at
    most one. No differentiation theorem is used. *)
Theorem scalar_rectangle_mass_obstruction_exists (R : realType) :
  exists (nu : set (scalar_metric_plane R) -> \bar R) (Z : set (scalar_metric_plane R)),
    is_measure nu /\
    (forall S, measure_measurable (@scalar_plane_lebesgue R) S -> measure_measurable nu S) /\
    scalar_plane_lebesgue Z = 1 /\ nu setT<=1 /\
    forall x, Z x -> forall e : R, (0<e)%R -> exists S,
      scalar_rectangle_relation x S /\ 2*scalar_plane_lebesgue S<=nu S /\
      extended_metric_diameter S<e%:E.
Proof.
pose cap n := ((n.+1%:R : R)^-1)%R.
pose b n := @density_dyadic_weight R n.
have hcap n : (0<cap n)%R by rewrite /cap invr_gt0 ltr0n.
have hb n : (0<b n)%R := @density_dyadic_weight_positive R n.
have hex n : exists w : (set (scalar_metric_plane R) -> \bar R)*set (set (scalar_metric_plane R)),
    is_small_rectangle_mass_cover (cap n) (b n) w.1 w.2.
  have [nu [C h]] := @small_rectangle_mass_cover_exists R (cap n) (b n) (hcap n) (hb n).
  by exists (nu,C).
pose w n := projT1 (cid (hex n)).
have hw n : is_small_rectangle_mass_cover (cap n) (b n) (w n).1 (w n).2 := projT2 (cid (hex n)).
pose m n := (w n).1.
pose C n := (w n).2.
have hm n : is_measure (m n) := small_rectangle_cover_measure (hw n).
have [nu hsum] := @measure_sum_exists R (scalar_metric_plane R) nat setT m.
pose N n := @scalar_unit_square R `\` (\bigcup_(S in C n) S).
pose W := \bigcup_(n in @setT nat) N n.
pose Z := @scalar_unit_square R `\` W.
have hW : scalar_plane_lebesgue W = 0.
  apply: (@measure_null_countable_union R (scalar_metric_plane R) nat
    (@scalar_plane_lebesgue R) (scalar_plane_lebesgue_is_measure R) setT N (countableP _)).
  move=> n _; exact: small_rectangle_cover_remainder (hw n).
have hZZ : scalar_plane_lebesgue (@scalar_unit_square R `\` Z)=0.
  apply: (@measure_null_subset R (scalar_metric_plane R) (@scalar_plane_lebesgue R)
    (scalar_plane_lebesgue_is_measure R) _ W) hW.
  move=> x [hx hnZ]; apply: contrapT=> hnW; apply: hnZ; by split.
have hZ : scalar_plane_lebesgue Z = 1.
  apply/eqP; rewrite eq_le; apply/andP; split.
  - rewrite -scalar_unit_square_area.
    apply: (@measure_mono R (scalar_metric_plane R) _ (scalar_plane_lebesgue_is_measure R)).
    by move=> x [].
  - rewrite -scalar_unit_square_area.
    exact: null_remainder_measure_cover_bound (scalar_plane_lebesgue_is_measure R) hZZ.
have hcost : nu setT<=1.
  rewrite hsum; apply: le_trans _ (density_dyadic_weights_sum_bound R).
  apply: nonnegative_sum_mono=> n _; exact: small_rectangle_cover_cost (hw n).
exists nu,Z; split.
- exact (@measure_sum_is_measure R (scalar_metric_plane R) nat setT m nu (fun n _ => hm n) hsum).
split.
- move=> S hS; apply: (@measure_sum_measurable R (scalar_metric_plane R) nat setT m nu S
    (fun n _ => hm n) hsum).
  move=> n _; exact (@small_rectangle_cover_measurable R (cap n) (b n) (m n) (C n) (hw n) S hS).
split=> //; split=> // x [hx hnW] e he.
have [n hn] := @real_reciprocal_below R e he.
have hxC : (\bigcup_(S in C n) S) x.
  apply: contrapT=> hnC; apply: hnW; exists n=> //; by split.
have [S hS hxS] := hxC; exists S; split.
- split=> //; exact (@small_rectangle_cover_rectangles R (cap n) (b n) (m n) (C n) (hw n) S hS).
split.
- apply: le_trans (@small_rectangle_cover_mass R (cap n) (b n) (m n) (C n) (hw n) S hS) _.
  exact (@measure_sum_component_bound R (scalar_metric_plane R) nat setT m nu n S hsum Logic.I).
- apply: le_lt_trans (@small_rectangle_cover_diameter R (cap n) (b n) (m n) (C n) (hw n) S hS) _.
  by rewrite lte_fin.
Qed.

(** Source for [scalar_rectangle_relation_not_vitali]: coordinate
    form of the complete counterexample in Federer 2.8.20,
    p. 152. This auxiliary theorem uses the maximum
    metric; EuclideanRectangleCounterexample.v supplies the book's
    Euclidean metric and the standard L^2 measure. *)
Theorem scalar_rectangle_relation_not_vitali (R : realType) :
  ~ @is_vitali_relation R (scalar_metric_plane R) (@scalar_plane_lebesgue R)
      (@scalar_rectangle_relation R).
Proof.
have [nu [Z [hn [hmeas [hZ [hcost hf]]]]]] := scalar_rectangle_mass_obstruction_exists R.
pose C x S := scalar_rectangle_relation x S /\ 2*scalar_plane_lebesgue S<=nu S.
apply: (@vitali_fine_mass_obstruction R (scalar_metric_plane R) (@scalar_plane_lebesgue R)
  nu (@scalar_rectangle_relation R) C Z 2 (scalar_plane_lebesgue_is_measure R) hn).
- by rewrite ltr0n.
- by move=> x S [].
- move=> x hx; apply: (covering_relation_fine_iff_small_diameter C x).2=> e he.
  have [S [hS [hm hd]]] := hf x hx e he; exists S; split=> //; by split.
- move=> S [x [_ hCS]].
  have [[_ hrect] _] := hCS.
  have [a [b [c [d [_ [_ ->]]]]]] := hrect.
  apply: hmeas; exact: scalar_closed_rectangle_measurable.
- by move=> S [x [_ [_ hS]]].
- apply: le_lt_trans hcost _; by rewrite hZ mule1 lte_fin ltr1n.
Qed.
