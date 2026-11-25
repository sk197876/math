(** Federer (1969), 3.3.13, pp. 297–298: original arbitrary
    finite-Hausdorff-mass decomposition, with every exponent retained. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  cardinality reals constructive_ereal topology.
From Federer Require Import EuclideanInnerProduct InnerMetric EuclideanProjectionSpace
  OrthogonalProjectionProbability HausdorffMeasure HausdorffClosedCoverAgreement IntegralGeometricMeasure IntegralGeometricNullSets
  StructureConeUP StructureProjectionConditions StructureProjectionDecomposition
  StructureHausdorffNullProjection StructureHausdorffFiniteFibres
  RectifiableSetUP PureUnrectifiableLaws SuslinSetUP BorelClosedProjection
  TopologicalBorel BorelRegularMeasureUP MeasureUP MeasureAlmostUP MeasureAlmostBasic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [structure_hausdorff_pure_decomposition]: the first
    assertion and Borel-regularity reduction of Federer 3.3.13,
    pp. 297–298. The same actual Borel rectifiable part works for
    every printed exponent. Original E need not be measurable.
    Actual 3.3.12 and actual 2.10.5 prove nullity of its original
    purely unrectifiable remainder; neither is a supplied hypothesis. *)
Theorem structure_hausdorff_pure_decomposition (R:realType) n m (hmn:(m<=n)%N)
    (E:set (inner_metric_space (@euclidean_inner_productP R n))):
  let H:=@hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R n)) m in
  H E< +oo ->exists B,borel_set B /\is_countably_m_rectifiable m B /\
    is_purely_measure_m_unrectifiable H m (E `\` B) /\
    forall t: \bar R,1<=t ->@integral_geometric_measure R n m hmn t (E `\` B)=0.
Proof.
cbn zeta; move=>hFinite.
pose X:=inner_metric_space (@euclidean_inner_productP R n).
pose H:=@hausdorff_measure R [the metricType R of X] m.
have hH:is_measure H:=@hausdorff_measure_is_measure R [the metricType R of X] m.
have hRegular:=@hausdorff_measure_borel_regular R [the metricType R of X] m.
have hStructure:is_structure_measure H.
  split; first exact:hH.
  move=>C hC; exact:(@borel_regular_borel_measurable R [the topologicalType of X] H hH hRegular C (closed_borel_set hC)).
have [F [hEF [hFBorel hEqual]]]:=borel_regular_cover hRegular E.
have hFFinite:H F< +oo by rewrite /H -hEqual.
have hFSuslin:is_suslin_set R F:=metric_borel_suslin hFBorel.
have hConditions:measure_almost_everywhere (@orthogonal_projection_probability R n m hmn)
    [set p|structure_projection_preserves_null_subsets H F p /\
      structure_projection_almost_finite_fibres F p].
  have hTheta:=theta_star_is_measure R hmn.
  apply:(measure_almost_everywhere_mono hTheta _ (measure_almost_everywhere_true hTheta)).
  move=>p _; split; first exact:structure_hausdorff_null_projection.
  exact:structure_hausdorff_almost_finite_fibres hFBorel hFFinite.
have [B [hBorel [hRectifiable [hPure hProjected]]]]:=
  @federer_3_3_12 R n m hmn H F hStructure hFSuslin hFFinite hConditions.
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
