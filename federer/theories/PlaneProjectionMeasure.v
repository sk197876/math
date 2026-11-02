(** Federer (1969), 2.5.10, p. 101: p(x)=x_1 on the Euclidean plane and its
    projected-counting integral. The measure used below is specified through
    the sealed Caratheodory construction, and its actual multiplicity
    formula is proved by 2.10.10, p. 176. Its domination by H^1 is the m=1
    projection case of 2.10.11, p. 176, using 2.10.7, p. 175. The local
    erratum, p. 2, book p. 101 line 15, corrects the projection's source
    point to R^2. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals
  constructive_ereal topology.
From Federer Require Import EuclideanInnerProduct InnerMetric RealMetricBackground
  ExtendedRealOrderTopology PartialFunctionBasic MeasureUP BorelRegularMeasureUP
  TopologicalBorel LebesgueScalarMeasure HausdorffLength EuclideanCoordinateMetric
  EuclideanPlaneMeasurableImages BorelImageCoverCost BorelCaratheodoryMeasure
  RealProjectionCoverBound MappingMultiplicity BorelMultiplicityIntegral MeasureIntegralUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [plane_first_projection]: direct coordinate
    projection p of Federer 2.5.10, p. 101, with
    the source corrected by the erratum p. 2,
    book p. 101 line 15. *)
Definition plane_first_projection (R : realType)
    (x : inner_metric_space (@euclidean_inner_productP R 2)) : real_line_metric R := x ord0.

(** Source for [plane_projection_measure]: the measure
    whose Borel-set integral is the fibre count in
    Federer 2.5.10, p. 101, constructed by
    2.10.10, p. 176, with cost L^1(p[S]). *)
Definition plane_projection_measure (R : realType) :=
  borel_caratheodory_measure
    (borel_image_cover_cost (@plane_first_projection R) (@lebesgue_scalar_measure R)).

(** Source for [plane_projection_is_measure]: supporting
    measure law of 2.10.10, p. 176, for the
    projection in Federer 2.5.10, p. 101. *)
Lemma plane_projection_is_measure (R : realType) : is_measure (@plane_projection_measure R).
Proof.
apply: borel_caratheodory_is_measure; exact: borel_image_cover_cost_laws (lebesgue_scalar_is_measure R).
Qed.

(** Source for [plane_projection_borel_regular]: Borel
    regularity of the Caratheodory measure in Federer
    2.10.10, p. 176, from 2.10.1, p. 170,
    supporting 2.5.10, p. 101. *)
Lemma plane_projection_borel_regular (R : realType) :
  is_borel_regular_measure (@plane_projection_measure R).
Proof.
apply: borel_caratheodory_borel_regular; exact: borel_image_cover_cost_laws (lebesgue_scalar_is_measure R).
Qed.

(** Source for [plane_projection_hausdorff_bound]: the
    setwise domination underlying the functional bound
    in Federer 2.5.10, p. 101, proved by
    2.10.7 and 2.10.11, pp. 175–176. *)
Lemma plane_projection_hausdorff_bound (R : realType) A :
  @plane_projection_measure R A<=hausdorff_length A.
Proof.
apply: real_projection_caratheodory_bound=> x y.
exact: euclidean_coordinate_nonexpanding.
Qed.

(** Source for [plane_projection_multiplicity_integral]:
    direct characteristic-set case of the functional
    formula in Federer 2.5.10, p. 101, using
    2.10.10, p. 176. The integral includes infinite
    multiplicities and the empty set. *)
Theorem plane_projection_multiplicity_integral (R : realType)
    (A : set (inner_metric_space (@euclidean_inner_productP R 2))) :
  borel_set A ->
  is_measure_integral (@lebesgue_scalar_measure R)
    (partial_function_total (fun t =>
      (@mapping_multiplicity R _ _ (@plane_first_projection R) A t : extended_real_line R)))
    (plane_projection_measure A).
Proof.
move=> hA; have [D [hD hd]] := euclidean_plane_separable R.
apply: (@borel_multiplicity_integral R
  [the metricType R of inner_metric_space (@euclidean_inner_productP R 2)] R
  (@plane_first_projection R) (@lebesgue_scalar_measure R)
  (lebesgue_scalar_is_measure R) D A hD hd _ hA).
move=> S hS; exact (@euclidean_plane_coordinate_borel_image R ord0 S hS).
Qed.
