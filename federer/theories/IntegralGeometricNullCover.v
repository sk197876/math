(** Supporting small Borel covers for Federer (1969), 2.10.5, p. 173, last
    paragraph: a Borel set whose projections have zero volume almost
    everywhere is null for every I_t. A zero cost on an unbounded set alone
    does not suffice for the diameter-restricted construction. Intersect the
    set with a countable small closed cover, using 2.2.8, p. 64, and then
    apply 2.10.1, p. 170. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  cardinality reals constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric EuclideanMetricSeparability
  EuclideanProjectionMetric OrthogonalProjectionProbability ProjectedVolumeMeasurability
  ProjectedVolumeBounds ProjectionBeta IntegralGeometricGauge IntegralGeometricMeasure
  NonnegativeExtendedExponentNorm NonnegativeExtendedNormZero MeasureAlmostUP MeasureAlmostBasic
  MeasureUP MeasureBasic SuslinSetUP BorelClosedProjection TopologicalBorel BorelFamilyBasic
  BorelCoverCostUP MetricDiameterUP MetricDiameter MetricScaleEnvelopeUP
  CaratheodoryLimitUP CaratheodoryBorelRegular SeparableClosedCover NonnegativeSum.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [integral_geometric_gauge_zero_iff]:
    supporting zero-cost criterion for Federer
    2.10.5, p. 173. Positive beta and the
    actual extended-input norm give zero precisely
    for almost everywhere zero projected volume. *)
Theorem integral_geometric_gauge_zero_iff (R : realType) (n m : nat)
    (hmn : (m<=n)%N)
    (S : set (inner_metric_space (@euclidean_inner_productP R n))) (t : \bar R) :
  is_suslin_set R S -> 1<=t ->
  (@integral_geometric_gauge R n m hmn t S=0 <->
   measure_almost_everywhere (@orthogonal_projection_probability R n m hmn)
     [set p | projected_volume_function (m:=m) S p=0]).
Proof.
move=> hS ht.
have hz := @nonnegative_extended_norm_zero_iff R _
  (@orthogonal_projection_probability R n m hmn) (@theta_star_is_measure R n m hmn)
  (projected_volume_function (m:=m) S) t
  (fun p => projected_volume_function_nonnegative S p) ht
  (@theta_star_projected_volume_measurable R n m hmn S hS).
split.
- move=> h; apply: hz.1.
  by rewrite -(@integral_geometric_gauge_normalized R n m hmn t ht S) h mule0.
- move=> h; by rewrite /integral_geometric_gauge (hz.2 h) mule0.
Qed.

(** Source for [projection_null_subset]: supporting
    hereditary projection-null property in Federer
    2.10.5, p. 173. Images and Lebesgue outer
    measure are monotone; the source subsets need
    not themselves be measurable. *)
Lemma projection_null_subset (R : realType) (n m : nat) (hmn : (m<=n)%N)
    (A B : set (inner_metric_space (@euclidean_inner_productP R n))) :
  A `<=` B ->
  measure_almost_everywhere (@orthogonal_projection_probability R n m hmn)
    [set p | projected_volume_function (m:=m) B p=0] ->
  measure_almost_everywhere (@orthogonal_projection_probability R n m hmn)
    [set p | projected_volume_function (m:=m) A p=0].
Proof.
move=> hAB hB; apply: (@measure_almost_everywhere_mono R _ _
  (@theta_star_is_measure R n m hmn) _ _ _ hB)=> p hp.
change (projected_volume_function (m:=m) A p=0).
apply/eqP; rewrite eq_le projected_volume_function_nonnegative andbT.
have hle := projected_volume_function_mono p hAB; by rewrite hp in hle.
Qed.

(** Source for [integral_geometric_borel_projection_null]:
    supporting reverse implication in Federer
    2.10.5, p. 173, last paragraph. Cover an
    arbitrary Borel set by countably many Borel
    subsets of prescribed small diameter and zero
    cost. No boundedness premise is added. *)
Theorem integral_geometric_borel_projection_null (R : realType) (n m : nat)
    (hmn : (m<=n)%N)
    (B : set (inner_metric_space (@euclidean_inner_productP R n))) (t : \bar R) :
  borel_set B -> 1<=t ->
  measure_almost_everywhere (@orthogonal_projection_probability R n m hmn)
    [set p | projected_volume_function (m:=m) B p=0] ->
  @integral_geometric_measure R n m hmn t B=0.
Proof.
move=> hB ht hz.
pose E := inner_metric_space (@euclidean_inner_productP R n).
pose J := @borel_metric_sets R E.
pose c (j : J) := @integral_geometric_gauge R n m hmn t (val j).
have hm := @integral_geometric_measure_is_measure R n m hmn t ht.
apply/eqP; rewrite eq_le (measure_nonnegative hm B) andbT.
apply: (caratheodory_limit_least (@integral_geometric_measure_specification R n m hmn t))=> delta nu hd hnu.
have [k hk] := reciprocal_metric_cutoffs_cofinal hd.
pose e : R := (((k.+1)%:R)^-1)%R.
have he : (0<e)%R by rewrite /e invr_gt0 ltr0n.
have [D [hD hDense]] := euclidean_metric_separable R n.
have hne : (@setT E) !=set0 by exists (0%R : R_n R n).
have [F [hF hcover]] := @separable_closed_small_cover R E D setT e hD hDense closedT hne he.
have hCF i : borel_set (B `&` F i).
  exact: (borel_family_binary_intersection (borel_sets_family E) hB (closed_borel_set (hF i).1)).
pose j (i : nat) : J := @exist _ (fun C : set E => C \in [set C : set E | borel_set C])
  (B `&` F i) (mem_set (hCF i)).
pose G := j @` setT.
have hG : countable G := sub_countable (card_image_le j setT) (countableP setT).
have hsize (a : J) : G a -> extended_metric_diameter (val a)<=delta.
  move=> [i _ <-]; apply: le_trans _ hk.
  apply: (metric_diameter_least (extended_metric_diameter_specification (B `&` F i))).
  - rewrite lee_fin; exact: ltW he.
  - move=> x y [_ hx] [_ hy]; rewrite lee_fin; exact: (hF i).2.2.2 x y hx hy.
have hcoverB : B `<=` \bigcup_(a in G) val a.
  move=> x hx; have hwhole : (\bigcup_i F i) x by rewrite -hcover.
  have [i _ hxi] := hwhole; exists (j i); first by exists i.
  by split.
have hcost (a : J) : G a -> c a=0.
  move=> [i _ <-]; apply: (@integral_geometric_gauge_zero_iff R n m hmn (B `&` F i) t
    (metric_borel_suslin (hCF i)) ht).2.
  exact: (@projection_null_subset R n m hmn (B `&` F i) B (fun x hx => hx.1) hz).
have hb := metric_scale_envelope_lower hnu hG hsize hcoverB.
by rewrite (nonnegative_sum_zero hcost) in hb.
Qed.
