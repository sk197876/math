(** Federer (1969), 3.3.18, p. 301: the complete first
    positive-density assertion for the original source and measure. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import EuclideanInnerProduct InnerMetric StructureConeUP
  StructureFiniteSourceRegularisation CountablyRectifiablePositiveUpperDensity
  RectifiableSetUP MetricDensities MeasureUP MeasureBasic MeasureSplit MeasureRestriction
  MeasureAlmostUP MeasureAlmostBasic MeasureDerivationContext BorelRegularMeasureUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [federer_3_3_18_positive_density]: the first assertion
    of Federer 3.3.18, p. 301. The ORIGINAL arbitrary finite-mass
    (phi,m) rectifiable E has positive ORIGINAL restricted upper
    density at phi almost every point. Actual finite regularisation,
    finite Hausdorff-mass rectifiable carriers, 2.10.19(1) and
    countable null assembly discharge the whole assertion. Infinite
    densities and natural degree zero remain; E need not be measurable. *)
Theorem federer_3_3_18_positive_density (R:realType) n m
    (phi:set (inner_metric_space (@euclidean_inner_productP R n))->\bar R)
    (E:set (inner_metric_space (@euclidean_inner_productP R n))):
  is_structure_measure phi ->is_measure_m_rectifiable phi m E ->
  measure_almost_everywhere_on phi E
    [set a|0<upper_metric_density m (measure_restrict phi E) a].
Proof.
move=>hStructure [[hPhi [S [hS hLoss]]] hFinite].
pose X:=inner_metric_space (@euclidean_inner_productP R n).
have [psi [hReg [hClass [hRadon [hTotal [hValue [hDomination hDensity]]]]]]]:=
  @structure_finite_source_regularisation R n m phi E hStructure hFinite.
have hPsi:=derivation_measure_law hClass.
have hRegular:=borel_regular_is_regular hPsi (derivation_measure_borel_regular hClass).
have hPositive:=@countably_rectifiable_positive_upper_density R n m psi S hPsi hRegular hS.
pose P:=[set a:X|0<upper_metric_density m psi a].
have hOriginalNull:phi (E `&` (S `\` P))= 0.
  have hBound:=hDomination (S `\` P); rewrite hPositive in hBound.
  apply/eqP; rewrite eq_le (measure_nonnegative hPhi) andbT; exact:hBound.
have hCover:E `\` [set a|0<upper_metric_density m (measure_restrict phi E) a] `<=`
    (E `\` S) `|` (E `&` (S `\` P)).
  move=>a [hE hn].
  have [hIn|hOut]:=pselect (S a); last by left; split.
  right; split; first exact:hE.
  split; first exact:hIn.
  move=>hP; apply:hn.
  change (is_true (0<upper_metric_density m (measure_restrict phi E) a)%E).
  rewrite -(hDensity a); exact:hP.
have hBound:=measure_binary_cover hPhi hCover.
rewrite hLoss hOriginalNull add0e in hBound.
apply/eqP; rewrite eq_le (measure_nonnegative hPhi) andbT; exact:hBound.
Qed.
