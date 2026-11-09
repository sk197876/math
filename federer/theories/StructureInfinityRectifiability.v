(** Federer (1969), 3.3.14, p. 298: the complete original
    finite-infinity-integral-geometric-mass rectifiability theorem. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import EuclideanInnerProduct InnerMetric EuclideanProjectionSpace
  OrthogonalProjectionProbability IntegralGeometricMeasure IntegralGeometricNullSets
  StructureConeUP StructureProjectionConditions StructureProjectionDecomposition
  StructureIntegralGeometricNullPreservation StructureIntegralGeometricFiniteFibres
  RectifiableSetUP SuslinSetUP BorelClosedProjection TopologicalBorel BorelRegularMeasureUP
  MeasureUP MeasureBasic MeasureAlmostUP MeasureAlmostBasic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [structure_infinity_borel_rectifiable_part]: the final
    application of 3.3.12 and 2.10.5 in Federer 3.3.14, p. 298.
    Both original projection hypotheses have been derived, including
    one common exception for EVERY original null subset. The original
    finite-mass Borel source has a countably m rectifiable Borel part
    with actual I-infinity-null original remainder. *)
Lemma structure_infinity_borel_rectifiable_part (R:realType) n m (hmn:(m<=n)%N)
    (E:set (inner_metric_space (@euclidean_inner_productP R n))):
  borel_set E ->@integral_geometric_measure R n m hmn +oo E< +oo ->
  exists B,borel_set B /\is_countably_m_rectifiable m B /\
    @integral_geometric_measure R n m hmn +oo (E `\` B)=0.
Proof.
move=>hE hFinite.
pose X:=inner_metric_space (@euclidean_inner_productP R n).
pose I:=@integral_geometric_measure R n m hmn +oo.
have hI:is_measure I:=@integral_geometric_measure_is_measure R n m hmn +oo (leey 1).
have hRegular:=@integral_geometric_measure_borel_regular R n m hmn +oo (leey 1).
have hStructure:is_structure_measure I.
  split; first exact:hI.
  move=>C hC; exact:(@borel_regular_borel_measurable R [the topologicalType of X]
    I hI hRegular C (closed_borel_set hC)).
have hTheta:=theta_star_is_measure R hmn.
have hConditions:=measure_almost_everywhere_and hTheta
  (@structure_integral_geometric_null_preservation R n m hmn E hE hFinite)
  (@structure_integral_geometric_finite_fibres R n m hmn E hE hFinite).
have [B [hBorel [hRectifiable [_ hProjected]]]]:=@federer_3_3_12 R n m hmn
  I E hStructure (metric_borel_suslin hE) hFinite hConditions.
exists B; split; first exact:hBorel.
split; first exact:hRectifiable.
apply:(@integral_geometric_projection_null_iff R n m hmn +oo (E `\` B) (leey 1)).2.
exists (E `\` B); split; first by move=>x hx.
split; first exact:borel_set_difference hE hBorel.
exact:hProjected.
Qed.

(** Source for [federer_3_3_14]: COMPLETE Federer 3.3.14, p. 298.
    Every original arbitrary E of finite actual I-infinity mass is
    (I-infinity,m) rectifiable. Retain every natural 0<=m<=n,
    original nonmeasurable sources, actual projection probability and
    original fibres. Actual finite Borel hulls, countable common
    projection tests, original null-subset preservation, original
    almost-finite fibres and the actual 3.3.12 decomposition are
    derived. No structure or rectifiability conclusion is a premise. *)
Theorem federer_3_3_14 (R:realType) n m (hmn:(m<=n)%N)
    (E:set (inner_metric_space (@euclidean_inner_productP R n))):
  let I:=@integral_geometric_measure R n m hmn +oo in
  I E< +oo ->is_measure_m_rectifiable I m E.
Proof.
cbn zeta; move=>hFinite.
pose X:=inner_metric_space (@euclidean_inner_productP R n).
pose I:=@integral_geometric_measure R n m hmn +oo.
have hI:is_measure I:=@integral_geometric_measure_is_measure R n m hmn +oo (leey 1).
have hRegular:=@integral_geometric_measure_borel_regular R n m hmn +oo (leey 1).
have [F [hEF [hBorel hEqual]]]:=borel_regular_cover hRegular E.
have hFFinite:I F< +oo by rewrite /I -hEqual.
have [B [hBBorel [hRectifiable hNull]]]:=
  @structure_infinity_borel_rectifiable_part R n m hmn F hBorel hFFinite.
have hSub:(E `\` B) `<=` (F `\` B).
  by move=>x [hx hn]; split; first exact:hEF x hx.
have hOriginalNull:I (E `\` B)=0.
  exact:(@measure_null_subset R [the choiceType of X] I hI _ _ hSub hNull).
split; last exact:hFinite.
split; first exact:hI.
exists B; by split.
Qed.
