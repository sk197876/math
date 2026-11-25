(** Federer (1969), 3.2.27, pp. 262–263: the
    projection multiplicity integrals of a finite measurable
    rectifiable source. The Borel sandwich of 2.2.3,
    p. 61, extends the actual 2.10.15 integrability
    statement to completed source sets. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric
  EuclideanProjectionSpace EuclideanProjectionMetric EuclideanLebesgueDimensions EuclideanHausdorffLebesgue
  PartialFunctionUP PartialFunctionBasic ProjectionMultiplicityIntegral MappingMultiplicity MappingMultiplicityLaws
  NullLipschitzArea LipschitzUP HausdorffMeasure HausdorffClosedCoverAgreement
  MeasureUP MeasureBasic MeasureAlmostUP MeasureAlmostBasic BorelRegularMeasureUP BorelRegularSandwich
  MeasureIntegralUP MeasureIntegralBounds MeasureIntegralUniqueness MeasureIntegralAlmostEquality
  TopologicalBorel ExtendedRealOrderTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [measurable_projection_multiplicity_integral]: the
    actual a_lambda integrability used in 3.2.27,
    p. 263. A Borel inner and outer sandwich differs
    by a Hausdorff-null set; its projection is Lebesgue-null.
    Outside that image the fibres agree exactly. No
    measurable-source hypothesis is silently inferred from
    finite rectifiability alone. *)
Theorem measurable_projection_multiplicity_integral (R:realType) m n
    (A:set (R_n R n)) (p:orthogonal_projection_metric_space R n m):
  measure_measurable (@hausdorff_measure R
    (inner_metric_space (@euclidean_inner_productP R n)) m) A ->
  @hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R n)) m A < +oo ->
  is_measure_integral (@euclidean_lebesgue_measure R m)
    (projection_multiplicity_integrand A p) (projection_multiplicity_integral A p).
Proof.
move=>hA hFinite.
pose X:=inner_metric_space (@euclidean_inner_productP R n).
pose Y:=inner_metric_space (@euclidean_inner_productP R m).
pose H:=@hausdorff_measure R X m.
pose beta:=@euclidean_lebesgue_measure R m.
pose F:=euclidean_projection_linear p.
have hH:=@hausdorff_measure_is_measure R X m.
have hBeta:=@euclidean_lebesgue_is_measure R m.
have [D [B [hD [hB [hDA [hAB hNull]]]]]]:=@borel_regular_finite_sandwich R X H hH
  (@hausdorff_measure_borel_regular R X m) A hA hFinite.
have hLipschitz:@is_metric_lipschitz_bound R X Y setT F 1%R.
  split; first exact:ler01; move=>x y _ _; rewrite mul1r; exact:euclidean_projection_nonexpanding.
have hNullImage:beta (F @` (B `\` D))=0.
  have h:=@null_hausdorff_lipschitz_image R X Y F 1%R m (B `\` D) hLipschitz hNull.
  by rewrite (euclidean_hausdorff_spherical_lebesgue (F @` (B `\` D))).1 in h.
have hAE:measure_almost_everywhere beta (~` (F @` (B `\` D))).
  by rewrite /measure_almost_everywhere setCK.
have hAgreement:measure_almost_equal beta (projection_multiplicity_integrand D p)
    (projection_multiplicity_integrand A p).
  apply:(measure_almost_everywhere_mono hBeta _ hAE)=>y hy.
  have hFibre:=@mapping_fibre_sandwich_equal (Choice.clone X _) Y F D A B y hDA hAB hy.
  exists (@mapping_multiplicity R (Choice.clone X _) Y F D y); split; first reflexivity.
  change (@mapping_multiplicity R (Choice.clone X _) Y F A y=
    @mapping_multiplicity R (Choice.clone X _) Y F D y).
  by rewrite /mapping_multiplicity hFibre.
have hIntegral:=measure_integral_almost_equal hBeta
  (@projection_multiplicity_integral_specification R n m D p hD) hAgreement.
have hValue:projection_multiplicity_integral A p=projection_multiplicity_integral D p.
  exact:(measure_lower_integral_unique (measure_lower_integral_specification beta
    (projection_multiplicity_integrand A p)) hIntegral.2.2).
by rewrite hValue.
Qed.
