(** Federer (1969), 3.3.16, p. 299: original arbitrary
    finite-replacement-mass decomposition, with every exponent retained. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  cardinality reals constructive_ereal topology.
From Federer Require Import EuclideanInnerProduct InnerMetric EuclideanProjectionSpace
  OrthogonalProjectionProbability StructureReplacementMeasureUP StructureDominatedProjectionFibres IntegralGeometricMeasure IntegralGeometricNullSets
  StructureConeUP StructureProjectionConditions StructureProjectionDecomposition
  RectifiableSetUP PureUnrectifiableLaws SuslinSetUP BorelClosedProjection
  TopologicalBorel BorelRegularMeasureUP MeasureUP MeasureAlmostUP MeasureAlmostBasic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [structure_replacement_pure_decomposition]: the
    original arbitrary-source decomposition in Federer 3.3.16,
    p. 299. Independent replacement comparisons, actual 2.10.8
    and 2.10.10 discharge both original projection conditions.
    Actual 3.3.12 on an equal-mass Borel hull and original outer
    monotonicity give the SAME Borel countably rectifiable part
    for EVERY final integral-geometric exponent. No finite
    Hausdorff mass or source measurability is added. *)
Theorem structure_replacement_pure_decomposition (R:realType) n m (hmn:(m<=n)%N)
    (phi:set (inner_metric_space (@euclidean_inner_productP R n))->\bar R)
    (E:set (inner_metric_space (@euclidean_inner_productP R n))):
  is_structure_replacement_measure m phi ->phi E< +oo ->
  exists B,borel_set B /\is_countably_m_rectifiable m B /\
    is_purely_measure_m_unrectifiable phi m (E `\` B) /\
    forall t: \bar R,1<=t ->@integral_geometric_measure R n m hmn t (E `\` B)=0.
Proof.
move=>hLaws hFinite.
pose X:=inner_metric_space (@euclidean_inner_productP R n).
have hH:is_measure phi:=structure_replacement_measure_law hLaws.
have hRegular:=structure_replacement_borel_regular hLaws.
have hStructure:is_structure_measure phi.
  split; first exact:hH.
  move=>C hC; exact:(@borel_regular_borel_measurable R [the topologicalType of X] phi hH hRegular C (closed_borel_set hC)).
have [F [hEF [hFBorel hEqual]]]:=borel_regular_cover hRegular E.
have hFFinite:phi F< +oo by rewrite -hEqual.
have hFSuslin:is_suslin_set R F:=metric_borel_suslin hFBorel.
have hConditions:measure_almost_everywhere (@orthogonal_projection_probability R n m hmn)
    [set p|structure_projection_preserves_null_subsets phi F p /\
      structure_projection_almost_finite_fibres F p].
  have hTheta:=theta_star_is_measure R hmn.
  apply:(measure_almost_everywhere_mono hTheta _ (measure_almost_everywhere_true hTheta)).
  move=>p _; exact:(@structure_dominated_projection_conditions R n m phi F p hLaws hFBorel hFFinite).
have [B [hBorel [hRectifiable [hPure hProjected]]]]:=
  @federer_3_3_12 R n m hmn phi F hStructure hFSuslin hFFinite hConditions.
have hSub:(E `\` B) `<=` (F `\` B) by move=>x [hx hn]; split; first exact:hEF hx.
have hBorelRemainder:borel_set (F `\` B).
  exact:borel_set_difference hFBorel hBorel.
exists B; split; first exact:hBorel.
split; first exact:hRectifiable.
split; first exact:pure_unrectifiable_subset hSub hPure.
move=>t ht.
have hNull:@integral_geometric_measure R n m hmn t (F `\` B)=0.
  apply:(@integral_geometric_projection_null_iff R n m hmn t (F `\` B) ht).2.
  exists (F `\` B); split; first by move=>x hx.
  split; first exact:hBorelRemainder.
  exact:hProjected.
exact:(@measure_null_subset R [the choiceType of X]
  (@integral_geometric_measure R n m hmn t)
  (@integral_geometric_measure_is_measure R n m hmn t ht) (E `\` B) (F `\` B) hSub hNull).
Qed.
