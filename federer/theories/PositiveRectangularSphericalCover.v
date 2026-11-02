(** Federer (1969), 2.10.39, printed p. 199: subdivide the first m-1 sides
    of a sorted box at its positive m-th side mesh, and bound the total
    spherical covering cost. This intermediate theorem is at a fixed strict
    cutoff. It does not assert a finite final measure for an arbitrary
    full-dimensional box when m<n. All choices use the existing opaque
    count, node and grid interfaces. Source context:
    ScalarSubdivisionCount.v. *)
From mathcomp Require Import all_boot all_order all_algebra reals classical_sets
  constructive_ereal topology ring lra.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric
  EuclideanBoxUP FinitePrefixes BoxSubdivisionCountsUP BoxSubdivisionCountsLaws
  BoxSubdivisionCounts PositiveBoxMeshBudget ScalarIntervalPartitionUP ScalarIntervalPartition
  RectangularGridUP RectangularGrid RectangularGridBallCover SphericalFiniteBallCover
  HausdorffMeasureUP HausdorffDiameterCost HausdorffRadiusCost EuclideanBallVolume
  MetricScaleEnvelopeUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [positive_rectangular_spherical_cutoff_bound]: direct
    positive-width box estimate in the proof of
    2.10.39, p. 199. Here m=p+1; the
    smallest of the first m sides is positive.
    The final norm-product replacement and zero-width
    limiting argument are performed separately. *)
Theorem positive_rectangular_spherical_cutoff_bound (R : realType) n p
    (hp : (p<n)%N) origin axis (c : 'I_n -> R) Q (d : R)
    (nu : set (inner_metric_space (@euclidean_inner_productP R n)) -> \bar R) :
  @is_euclidean_rectangular_box R n origin axis c Q ->
  (forall i j : 'I_n, (i<=j)%N -> c j<=c i) ->
  0<c (Ordinal hp) -> Num.sqrt n%:R*c (Ordinal hp)<d ->
  is_metric_scale_envelope
    (fun j : @positive_closed_metric_balls R
      [the metricType R of inner_metric_space (@euclidean_inner_productP R n)]=>val j)
    (fun j=>hausdorff_diameter_cost p.+1 (val j)) d%:E nu ->
  (nu Q<=(hausdorff_normalisation R p.+1*(Num.sqrt n%:R)^+p.+1*2^+p*
    \prod_(i<p.+1) family_prefix hp c i)%:E)%E.
Proof.
move=> hQ hsort hpos hcap hn.
pose h := c (Ordinal hp).
have hlong (i : 'I_n) : (i<p)%N -> h<=c i.
  move=> hi; exact: hsort i (Ordinal hp) (ltnW hi).
pose count := @box_subdivision_counts R n c p h hpos hlong.
have hcount := @box_subdivision_counts_specification R n c p h hpos hlong.
have hsmall (i : 'I_n) : (p<=i)%N -> c i<=h.
  move=> hi; exact: hsort (Ordinal hp) i hi.
have hw := box_subdivision_cell_width_bound hcount hsmall.
have hc i := euclidean_box_width_nonnegative_law hQ i.
have hk i := box_subdivision_count_positive_law hcount i.
pose node i := @equal_interval_partition R (c i) (count i) (hc i) (hk i).
have hP i := @equal_interval_partition_specification R (c i) (count i) (hc i) (hk i).
have he := euclidean_box_orthonormal_law hQ.
pose centre : rectangular_grid_indices count ->
    inner_metric_space (@euclidean_inner_productP R n) :=
  @rectangular_grid_centres R n origin axis count node he.
have hG := @rectangular_grid_centres_specification R n origin axis count node he.
have hcover := rectangular_grid_ball_cover hQ hP hG (ltW hpos) hw.
pose r := Num.sqrt n%:R*h/2.
have hr : 0<=r by rewrite /r divr_ge0 ?ler0n //; exact: mulr_ge0 (sqrtr_ge0 _) (ltW hpos).
have hdiam : r+r<d.
  have hrr : r+r=Num.sqrt n%:R*h by rewrite /r; lra.
  by rewrite hrr.
have hballs := @spherical_cutoff_finite_equal_ball_cover R
  [the metricType R of inner_metric_space (@euclidean_inner_productP R n)]
  (rectangular_grid_indices count) p.+1 centre r d nu Q hn hr hdiam hcover.
have hbudget := @positive_box_mesh_budget R n p hp c h count hcount erefl.
have hg : euclidean_unit_ball_volume R p.+1*r^+p.+1=
    hausdorff_normalisation R p.+1*(Num.sqrt n%:R)^+p.+1*h^+p.+1.
  rewrite -(@hausdorff_doubled_radius_normalisation R p.+1 r).
  have hrr : r+r=Num.sqrt n%:R*h by rewrite /r; lra.
  by rewrite hrr exprMn mulrA.
have ha : 0<=hausdorff_normalisation R p.+1*(Num.sqrt n%:R)^+p.+1.
  exact: mulr_ge0 (ltW (hausdorff_normalisation_positive R p.+1))
    (exprn_ge0 _ (sqrtr_ge0 _)).
have hb := ler_wpM2l ha hbudget.
have hcost : #|rectangular_grid_indices count|%:R*
    (euclidean_unit_ball_volume R p.+1*r^+p.+1)<=
  hausdorff_normalisation R p.+1*(Num.sqrt n%:R)^+p.+1*2^+p*
    \prod_(i<p.+1) family_prefix hp c i.
  rewrite hg.
  have heq : #|rectangular_grid_indices count|%:R*
      (hausdorff_normalisation R p.+1*(Num.sqrt n%:R)^+p.+1*h^+p.+1)=
    (hausdorff_normalisation R p.+1*(Num.sqrt n%:R)^+p.+1)*
      (#|rectangular_grid_indices count|%:R*h^+p.+1) by ring.
  rewrite heq; move: hb; by rewrite !mulrA.
apply: le_trans hballs _; by rewrite lee_fin.
Qed.
