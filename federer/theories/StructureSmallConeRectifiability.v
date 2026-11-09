(** Federer (1969), 3.3.17, pp. 300–301: the complete
    ORIGINAL small-cone-density rectifiability criterion. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets cardinality
  reals constructive_ereal topology.
From Federer Require Import EuclideanInnerProduct InnerMetric EuclideanProjectionSpace EuclideanProjectionMetric
  StructureConeUP StructureSmallConeCriterionUP StructureFiniteSourceRegularisation
  StructureRegularisedConeDensities StructureSmallConeLocalTests StructureRationalConeTests
  StructureCountablePureTestsNull RectifiableSetUP RectifiablePureDecomposition
  MeasureDerivationContext MeasureUP MeasureBasic MeasureSplit MeasureAlmostUP MeasureAlmostBasic
  BorelRegularMeasureUP TopologicalBorel.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [federer_3_3_17]: COMPLETE Federer 3.3.17,
    pp. 300–301. The standing original measure measures closed
    sets, original phi(E) is finite, and at phi almost every
    original a in E some original (n-m)-plane and aperture
    0<s<1 have upper conical density strictly below
    c*s^m times original upper density, c= 1/(2*84^m).
    Then ORIGINAL E is (phi,m) rectifiable. All natural
    0<=m<=n and infinite original upper densities remain.
    The actual regularisation, countably rectifiable Borel part,
    countable dense projection family, rational cone tests,
    relative density-one transfer and pure-set nullity are
    derived. No original measurability, finite density, selected
    plane field or supplied structure conclusion is added. *)
Theorem federer_3_3_17 (R:realType) n m (hmn:(m<=n)%N)
    (phi:set (inner_metric_space (@euclidean_inner_productP R n))->\bar R)
    (E:set (inner_metric_space (@euclidean_inner_productP R n))):
  is_structure_measure phi ->phi E< +oo ->
  is_structure_small_cone_density_criterion m phi E ->is_measure_m_rectifiable phi m E.
Proof.
move=>hStructure hFinite hCriterion.
pose X:=inner_metric_space (@euclidean_inner_productP R n).
have [psi [hReg [hClass [hRadon [hTotal [hValue [hDomination hDensity]]]]]]]:=
  @structure_finite_source_regularisation R n m phi E hStructure hFinite.
have hPsi:=derivation_measure_law hClass.
have hRegular:=derivation_measure_borel_regular hClass.
have hPsiFinite:psi setT< +oo by rewrite hTotal.
have hClosed C:closed C ->measure_measurable psi C.
  move=>hC; exact:(borel_regular_borel_measurable hPsi hRegular (closed_borel_set hC)).
have [B [hB [hRect hPure]]]:=@rectifiable_pure_borel_decomposition R [the metricType R of X]
  psi m setT hPsi hPsiFinite hClosed.
have [D [hD hDense]]:=orthogonal_projection_metric_separable R n m.
pose U:=structure_countable_cone_tests hmn psi D.
have hUNull:psi (U `\` B)= 0:=@structure_countable_pure_tests_null R n m hmn psi D B
  hClass hPsiFinite hD hPure.
have hOriginalUnionNull:phi (E `&` (U `\` B))= 0.
  have hBound:=hDomination (U `\` B); rewrite hUNull in hBound.
  apply/eqP; rewrite eq_le (measure_nonnegative hStructure.1) andbT; exact:hBound.
pose Bad:=E `\` [set a|structure_small_cone_density_at m phi E a].
have hBad:phi Bad= 0:=hCriterion.
have hCover:E `\` B `<=` Bad `|` (E `&` (U `\` B)).
  move=>a [hE hnB].
  have [hGood|hNotGood]:=pselect (structure_small_cone_density_at m phi E a); last by left; split.
  right; split; first exact:hE.
  split; last exact:hnB.
  have [p [s [hS hSmall]]]:=@structure_regularised_small_cone_criterion R n m hmn phi psi E a
    hValue (hDensity a) hGood.
  have [lam [delta [hLam [hDelta hTest]]]]:=@structure_small_cone_actual_local_test R n m hmn psi p a s hPsi hS hSmall.
  exact:(@structure_local_test_in_countable_union R n m hmn psi D p a s lam delta
    hPsi hDense hS hLam hDelta hTest).
have hRemainderNull:phi (E `\` B)= 0.
  have hBound:=measure_binary_cover hStructure.1 hCover.
  rewrite hBad hOriginalUnionNull add0e in hBound.
  apply/eqP; rewrite eq_le (measure_nonnegative hStructure.1) andbT; exact:hBound.
split; last exact:hFinite.
split; first exact:hStructure.1.
exists B; by split.
Qed.
