(** Federer (1969), 3.3.18, p. 301: actual positive
    Hausdorff examples for the complete density and tangent theorem. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets cardinality
  reals constructive_ereal topology.
From Federer Require Import EuclideanInnerProduct InnerMetric StructureConeUP
  StructureMeasureRectifiableTangents StructureSmallConeConverseCounterexample
  StructureSmallConeCriterionUP MeasureSupport RectifiableSetUP MetricDensities MeasureRestriction
  MeasureUP MeasureAlmostUP MeasureAlmostBasic PartialFunctionUP BorelRegularMeasureUP TopologicalBorel
  HausdorffMeasure HausdorffClosedCoverAgreement HausdorffRestrictedDensity
  EuclideanOpenUnitCube EuclideanUnitCubeRectifiable EuclideanLebesgueDimensions.
From FedererTests Require Import StructureSmallConeExamples.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [finite_hausdorff_rectifiable_full_tangent_conclusion]:
    actual Hausdorff specialization of COMPLETE Federer 3.3.18,
    p. 301. Actual 2.10.19(5) derives the finite restricted
    upper-density premise. No measurability of the original E
    is needed and the complete tangent/normal/aperture data remain. *)
Lemma finite_hausdorff_rectifiable_full_tangent_conclusion (R:realType) n m (hmn:(m<=n)%N)
    (E:set (inner_metric_space (@euclidean_inner_productP R n))):
  let H:=@hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R n)) m in
  is_measure_m_rectifiable H m E ->
  measure_almost_everywhere_on H E [set a|0<upper_metric_density m (measure_restrict H E) a] /\
  measure_almost_everywhere_on H E [set a|
    structure_measure_rectifiable_tangent_point m (measure_restrict H E) a].
Proof.
move=>H hRect.
pose X:=inner_metric_space (@euclidean_inner_productP R n).
have hH:is_measure H:=@hausdorff_measure_is_measure R [the metricType R of X] m.
have hStructure:is_structure_measure H.
  split; first exact:hH.
  move=>C hC; exact:(borel_regular_borel_measurable hH
    (@hausdorff_measure_borel_regular R [the metricType R of X] m) (closed_borel_set hC)).
have hGlobal:=@finite_hausdorff_restricted_upper_density R [the metricType R of X] m E hRect.2.
have hFinite:measure_almost_everywhere_on H E [set a|upper_metric_density m (measure_restrict H E) a< +oo].
  apply:(measure_null_subset hH _ hGlobal)=>a [ha hn] hUpper; apply:hn.
  exact:le_lt_trans hUpper (ltry 1%R).
have hFull:=@federer_3_3_18 R n m hmn H E hStructure hRect.
split; first exact:hFull.1.
exact:hFull.2 hFinite.
Qed.

(** Source for [measure_rectifiable_tangent_positive_zero_atom]:
    actual positive R^0 Hausdorff atom in COMPLETE Federer
    3.3.18, p. 301. Mass one prevents vacuous null-source
    coverage; original degree zero and every aperture remain. *)
Example measure_rectifiable_tangent_positive_zero_atom (R:realType):
  let E:=@euclidean_open_unit_cube R 0 in
  let H:=@hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R 0)) 0 in
  H E= 1 /\measure_almost_everywhere_on H E [set a|
    structure_measure_rectifiable_tangent_point 0 (measure_restrict H E) a].
Proof.
cbn zeta; have [hRect [_ hMass]]:=@euclidean_open_unit_cube_measure_rectifiable R 0.
split; first exact:hMass.
exact:(@finite_hausdorff_rectifiable_full_tangent_conclusion R 0 0 (leqnn 0) _ hRect).2.
Qed.

(** Source for [measure_rectifiable_tangent_positive_unit_interval]:
    actual positive unit line interval in COMPLETE Federer
    3.3.18, p. 301. Actual finite upper density is derived,
    and original tangent, normal and all apertures remain. *)
Example measure_rectifiable_tangent_positive_unit_interval (R:realType):
  let E:=@euclidean_open_unit_cube R 1 in
  let H:=@hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R 1)) 1 in
  H E= 1 /\measure_almost_everywhere_on H E [set a|
    structure_measure_rectifiable_tangent_point 1 (measure_restrict H E) a].
Proof.
cbn zeta; have [hRect [_ hMass]]:=@euclidean_open_unit_cube_measure_rectifiable R 1.
split; first exact:hMass.
exact:(@finite_hausdorff_rectifiable_full_tangent_conclusion R 1 1 (leqnn 1) _ hRect).2.
Qed.

(** Source for [measure_rectifiable_tangent_original_nonmeasurable_source]:
    actual original nonmeasurable positive finite-mass source from
    2.2.4 in COMPLETE Federer 3.3.18, p. 301. No measurable
    source replaces it. Actual finite upper density is derived
    before invoking the complete original tangent assertion. *)
Example measure_rectifiable_tangent_original_nonmeasurable_source (R:realType):
  exists E:set (inner_metric_space (@euclidean_inner_productP R 1)),
    ~measure_measurable (@euclidean_lebesgue_measure R 1) E /\
    (0<@hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R 1)) 1 E< +oo)%E /\
    measure_almost_everywhere_on (@hausdorff_measure R
      (inner_metric_space (@euclidean_inner_productP R 1)) 1) E [set a|
      structure_measure_rectifiable_tangent_point 1 (measure_restrict
        (@hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R 1)) 1) E) a].
Proof.
have [E [hNot [hMass [hCriterion hRect]]]]:=@small_cone_original_nonmeasurable_source R.
exists E; split; first exact:hNot.
split; first exact:hMass.
exact:(@finite_hausdorff_rectifiable_full_tangent_conclusion R 1 1 (leqnn 1) E hRect).2.
Qed.

(** Source for [measure_rectifiable_countable_support_converse_failure]:
    ACTUAL converse counterexample for Federer 3.3.18, p. 301.
    The finite positive planar measure has COUNTABLE TOPOLOGICAL
    SUPPORT and is measure-rectifiable on the whole original plane,
    while the original small-cone criterion fails on its positive
    atom. Every plane and aperture has actual infinite conical
    density there; no failure or infinite density is supplied. *)
Example measure_rectifiable_countable_support_converse_failure (R:realType):
  exists mu:set (inner_metric_space (@euclidean_inner_productP R 2))->\bar R,
    is_structure_measure mu /\(0<mu setT< +oo)%E /\
    countable (measure_support mu) /\is_measure_m_rectifiable mu 1 setT /\
    ~is_structure_small_cone_density_criterion 1 mu setT.
Proof. exact:structure_small_cone_converse_counterexample. Qed.
