(** Federer (1969), 3.3.17, pp. 300–301: actual positive
    atoms, unit interval, original nonmeasurable source and infinite density. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology lra.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric InnerNorm
  Hom TensorUP OrthogonalMaps CoordinateProjection ProjectedVolumeGauge EuclideanProjectionSpace EuclideanLebesgueDimensions
  StructureConeUP StructureCone StructureConeBasic StructureProjectionKernel StructureProjectionCone
  StructureSmallConeCriterionUP StructureSmallConeRectifiability RectifiableSetUP
  EuclideanOpenUnitCube EuclideanUnitCubeRectifiable HausdorffMeasure HausdorffClosedCoverAgreement
  FiniteHausdorffPositiveUpperDensity PointMassUpperLineDensity PointMassMeasure PointMassRegularity
  MetricDensities MetricDensityZeroUnions PartialFunctionUP MeasureRestriction
  MeasureUP MeasureBasic MeasureAlmostUP MeasureAlmostBasic BorelRegularMeasureUP TopologicalBorel.
From FedererTests Require Import StructureHausdorffStructureExamples.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [identity_projection_half_aperture_cone_empty]:
    actual regression support for the hypothesis in Federer
    3.3.17, p. 300. The original identity projection has zero
    kernel and its aperture-one-half cone is empty at every
    original radius. This includes ambient dimension zero. *)
Lemma identity_projection_half_aperture_cone_empty (R:realType) n
    (p:euclidean_projection_space R n n):
  (forall x,euclidean_projection_linear p x=x) ->
  forall (a:inner_metric_space (@euclidean_inner_productP R n)) r,
    structure_cone (structure_projection_kernel (leqnn n) p) a r (1/2)%R=set0.
Proof.
move=>hIdentity a r; apply/seteqP; split=>x; last by case.
move=>hx; have [hAngle hRadius]:=(@structure_projection_coneE R n n (leqnn n) p a r (1/2)%R x).1 hx.
rewrite hIdentity invf_div divr1 in hAngle.
have hNorm:=@inner_norm_nonnegative R (R_n R n) (@euclidean_inner_product R n)
  (@euclidean_inner_productP R n) (x-a).
have h12:((1:R)<=2)%R by rewrite ler1n.
have hDouble:=ler_wpM2r hNorm h12.
rewrite mul1r in hDouble.
by have:=lt_le_trans hAngle hDouble; rewrite ltxx.
Qed.

(** Source for [finite_full_dimensional_hausdorff_small_cone]:
    actual regression support for COMPLETE Federer 3.3.17,
    pp. 300–301. The identity projection gives an actual
    empty cone and actual 2.10.19(2) supplies positive original
    restricted density. Apply the COMPLETE new theorem to every
    original finite-Hausdorff-mass source, without measurability. *)
Lemma finite_full_dimensional_hausdorff_small_cone (R:realType) n
    (E:set (inner_metric_space (@euclidean_inner_productP R n))):
  let H:=@hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R n)) n in
  H E< +oo ->is_structure_small_cone_density_criterion n H E /\is_measure_m_rectifiable H n E.
Proof.
cbn zeta; move=>hFinite.
pose X:=inner_metric_space (@euclidean_inner_productP R n).
pose H:=@hausdorff_measure R [the metricType R of X] n.
have hH:is_measure H:=@hausdorff_measure_is_measure R [the metricType R of X] n.
have hStructure:is_structure_measure H.
  split; first exact:hH.
  move=>C hC; exact:(borel_regular_borel_measurable hH
    (@hausdorff_measure_borel_regular R [the metricType R of X] n) (closed_borel_set hC)).
have hp:O_star (linear_id (R_n R n)).
  exists (linear_id (R_n R n)); split; by move=>x y.
have [p hIdentity]:=euclidean_projection_linear_complete hp.
have hCone a r:=@identity_projection_half_aperture_cone_empty R n p hIdentity a r.
have hPositive:=@finite_hausdorff_positive_upper_density R [the metricType R of X] n E hFinite.
have hCriterion:is_structure_small_cone_density_criterion n H E.
  apply:(@measure_null_subset R [the choiceType of X] H hH _ _ _ hPositive).
  move=>a [ha hnCriterion]; split; first exact:ha.
  move=>hDensity; apply:hnCriterion.
  exists (structure_projection_kernel (leqnn n) p),(1/2)%R.
  split; first by apply/andP; split; lra.
  rewrite (hCone a +oo) setI0.
  have hZero:=(@metric_density_graph R [the metricType R of X] n (measure_restrict H set0) a 0).1
    (@metric_restricted_density_zero_empty R [the metricType R of X] n H a hH).
  rewrite hZero.1.
  have hCoefficient:(0<(structure_small_cone_constant R n*(1/2)^+n)%R%:E)%E.
    rewrite lte_fin; apply:mulr_gt0; first exact:structure_small_cone_constant_positive.
    apply:exprn_gt0; lra.
  exact:mule_gt0 hCoefficient hDensity.
split; first exact:hCriterion.
exact:(@federer_3_3_17 R n n (leqnn n) H E hStructure hFinite hCriterion).
Qed.

(** Source for [small_cone_positive_zero_atom]: the actual
    positive R^0 unit atom of mass one in COMPLETE Federer
    3.3.17, pp. 300–301. Verify the original criterion and
    retain both zero dimensions in the complete conclusion. *)
Example small_cone_positive_zero_atom (R:realType):
  let E:=@euclidean_open_unit_cube R 0 in
  let H:=@hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R 0)) 0 in
  H E= 1 /\is_structure_small_cone_density_criterion 0 H E /\is_measure_m_rectifiable H 0 E.
Proof.
cbn zeta; have hMass:=(@euclidean_open_unit_cube_measure_rectifiable R 0).2.2.
split; first exact:hMass.
apply:finite_full_dimensional_hausdorff_small_cone; by rewrite hMass ltry.
Qed.

(** Source for [small_cone_positive_unit_interval]: actual
    positive open unit line interval of mass one in COMPLETE
    Federer 3.3.17, pp. 300–301. The actual criterion,
    original source and complete conclusion are all retained. *)
Example small_cone_positive_unit_interval (R:realType):
  let E:=@euclidean_open_unit_cube R 1 in
  let H:=@hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R 1)) 1 in
  H E= 1 /\is_structure_small_cone_density_criterion 1 H E /\is_measure_m_rectifiable H 1 E.
Proof.
cbn zeta; have hMass:=(@euclidean_open_unit_cube_measure_rectifiable R 1).2.2.
split; first exact:hMass.
apply:finite_full_dimensional_hausdorff_small_cone; by rewrite hMass ltry.
Qed.

(** Source for [small_cone_original_nonmeasurable_source]: ACTUAL
    original nonmeasurable positive finite-mass line source from
    2.2.4 in COMPLETE Federer 3.3.17, pp. 300–301. Actual
    positive upper density and the actual identity cone verify
    the original criterion; no measurable source replaces E. *)
Example small_cone_original_nonmeasurable_source (R:realType):
  exists E:set (inner_metric_space (@euclidean_inner_productP R 1)),
    ~measure_measurable (@euclidean_lebesgue_measure R 1) E /\
    (0<@hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R 1)) 1 E< +oo) /\
    is_structure_small_cone_density_criterion 1
      (@hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R 1)) 1) E /\
    is_measure_m_rectifiable (@hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R 1)) 1) 1 E.
Proof.
have [E [hNot [hMass hAll]]]:=@structure_hausdorff_original_nonmeasurable_source R.
exists E; split; first exact:hNot.
split; first exact:hMass.
exact:(@finite_full_dimensional_hausdorff_small_cone R 1 E (andP hMass).2).
Qed.

(** Source for [small_cone_positive_atom_infinite_density]: actual
    positive unit atom in R^2 at degree one in COMPLETE Federer
    3.3.17, pp. 300–301. Its ORIGINAL upper density is proved
    infinite. The original cone excludes its vertex, so the
    conical density is zero and the ORIGINAL criterion holds
    with the exact coefficient. Keep genuine codimension one. *)
Example small_cone_positive_atom_infinite_density (R:realType):
  let a:inner_metric_space (@euclidean_inner_productP R 2):= 0%R in
  let phi:=point_mass R a in
  phi [set a]= 1 /\upper_metric_density 1 (measure_restrict phi [set a]) a=+oo /\
  is_structure_small_cone_density_criterion 1 phi [set a] /\is_measure_m_rectifiable phi 1 [set a].
Proof.
cbn zeta.
pose X:=inner_metric_space (@euclidean_inner_productP R 2).
pose a:X:= 0%R.
pose phi:=point_mass R a.
have hPhi:is_structure_measure phi.
  split; first exact:point_mass_is_measure.
  move=>C _; exact:point_mass_every_set_measurable.
have hMass:phi [set a]= 1 by apply:point_mass_in; by [].
have hInfinite:=@point_mass_upper_degree_one_density_infinite R [the metricType R of X] a.
have [f hf]:=@euclidean_projection_exists R 2 1 (leqnSn 1).
have [p hEval]:=euclidean_projection_linear_complete hf.
have hCriterion:is_structure_small_cone_density_criterion 1 phi [set a].
  have hEvery x:[set a] x ->structure_small_cone_density_at 1 phi [set a] x.
    move=>->; exists (structure_projection_kernel (leqnSn 1) p),(1/2)%R.
    split; first by apply/andP; split; lra.
    have hEmpty:[set a] `&` structure_cone (structure_projection_kernel (leqnSn 1) p) a +oo (1/2)%R=set0.
      apply/seteqP; split=>y; last by case.
      by move=>[-> hCone]; exact:structure_cone_vertex_excluded hCone.
    rewrite hEmpty.
    have hZero:=(@metric_density_graph R [the metricType R of X] 1 (measure_restrict phi set0) a 0).1
      (@metric_restricted_density_zero_empty R [the metricType R of X] 1 phi a hPhi.1).
    rewrite hZero.1 hInfinite.
    have hCoefficient:(0<(structure_small_cone_constant R 1*(1/2)^+1)%R%:E)%E.
      rewrite lte_fin; apply:mulr_gt0; first exact:structure_small_cone_constant_positive.
      apply:exprn_gt0; lra.
    exact:mule_gt0 hCoefficient (ltry _).
  have hEmpty:[set a] `\` [set x|structure_small_cone_density_at 1 phi [set a] x]=set0.
    apply/seteqP; split=>x; last by case.
    by move=>[hx hn]; exact:hn (hEvery x hx).
  rewrite /is_structure_small_cone_density_criterion /measure_almost_everywhere_on hEmpty.
  exact:measure_empty hPhi.1.
split; first exact:hMass.
split; first exact:hInfinite.
split; first exact:hCriterion.
apply:(@federer_3_3_17 R 2 1 (leqnSn 1) phi [set a] hPhi _ hCriterion).
by rewrite hMass ltry.
Qed.
