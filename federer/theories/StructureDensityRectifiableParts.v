(** Federer (1969), 3.3.15, p. 299: actual contained
    Borel rectifiable parts of the original upper-density strata. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import EuclideanInnerProduct InnerMetric EuclideanProjectionSpace EuclideanLebesgueDimensions
  OrthogonalProjectionProbability StructureConeUP StructureDensityStrata StructureDensityProjectionConditions
  StructureProjectionDecomposition StructureProjectionConditions RectifiableSetUP RectifiableElementary
  SuslinSetUP BorelClosedProjection TopologicalBorel BorelFamilyBasic BorelRegularMeasureUP
  MeasureUP MeasureBasic MeasureAlmostUP MeasureAlmostBasic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [structure_density_rectifiable_part]: the actual R_i
    contained in E_i in Federer 3.3.15, p. 299. Derive every original
    projection condition and apply complete 3.3.12. Intersect the
    resulting Borel part with the original Borel E_i, retaining its
    exact original pure remainder and projected-null image. No
    rectifiable family is supplied as a final theorem hypothesis. *)
Theorem structure_density_rectifiable_part (R:realType) n m (hmn:(m<=n)%N)
    (psi:set (inner_metric_space (@euclidean_inner_productP R n))->\bar R) i:
  is_measure psi ->is_borel_regular_measure psi ->psi setT< +oo ->
  let E:=structure_upper_density_stratum m psi i in
  exists B,B `<=` E /\borel_set B /\is_countably_m_rectifiable m B /\
    is_purely_measure_m_unrectifiable psi m (E `\` B) /\
    measure_almost_everywhere (@orthogonal_projection_probability R n m hmn)
      [set p|euclidean_lebesgue_measure m (euclidean_projection_linear p @` (E `\` B))=0].
Proof.
move=>hPsi hRegular hFinite; cbn zeta.
pose X:=inner_metric_space (@euclidean_inner_productP R n).
pose E:=structure_upper_density_stratum m psi i.
have hE:borel_set E:=@structure_density_stratum_borel R [the metricType R of X] m psi i hPsi.
have hEFinite:psi E< +oo:=le_lt_trans (@measure_mono R _ psi hPsi E setT (subsetT E)) hFinite.
have hStructure:is_structure_measure psi.
  split; first exact:hPsi.
  move=>C hC; exact:(@borel_regular_borel_measurable R [the topologicalType of X]
    psi hPsi hRegular C (closed_borel_set hC)).
have hTheta:=theta_star_is_measure R hmn.
have hConditions:measure_almost_everywhere (@orthogonal_projection_probability R n m hmn)
    [set p|structure_projection_preserves_null_subsets psi E p /\structure_projection_almost_finite_fibres E p].
  apply:(measure_almost_everywhere_mono hTheta _ (measure_almost_everywhere_true hTheta))=>p _.
  exact:(@structure_density_stratum_projection_conditions R n m psi i hPsi hRegular hFinite p).
have [B [hBorel [hRectifiable [hPure hProjected]]]]:=@federer_3_3_12 R n m hmn
  psi E hStructure (metric_borel_suslin hE) hEFinite hConditions.
pose Q:=E `&` B.
have hDifference:E `\` Q=E `\` B.
  apply/seteqP; split=>x; rewrite /Q /=; tauto.
exists Q; split; first by move=>x [hx _].
split.
- exact:(@borel_family_binary_intersection [the topologicalType of X] setT _
    (borel_sets_family [the topologicalType of X]) E B hE hBorel).
split.
- apply:countably_rectifiable_subset _ hRectifiable; by move=>x [_ hx].
split; first by rewrite hDifference.
by rewrite hDifference.
Qed.
