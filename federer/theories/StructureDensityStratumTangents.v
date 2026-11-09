(** Federer (1969), 3.3.18, p. 301: actual tangent
    planes on each original bounded rectifiable density stratum. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerNorm InnerMetric
  HilbertFormCompactness RectifiableSetUP RectifiableElementary RectifiableFiniteHausdorffMass
  RectifiableDensityTangent RectifiableTangentPlaneUP MeasureApproximateTangentUP
  ComparableMeasureTangents RestrictedApproximateTangent StructureRectifiableDensityStrata
  StructureDensityStratumLocality FiniteUpperDensityHausdorffBound
  MeasureUP MeasureBasic MeasureRestriction MeasureAlmostUP MeasureAlmostBasic
  MeasureDerivationContext BorelRegularMeasureUP TopologicalBorel HausdorffMeasure HausdorffClosedCoverAgreement
  MetricDensities PartialFunctionUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [structure_density_stratum_tangent_agreement]: the
    second exact tangent equality in Federer 3.3.18, p. 301.
    The proved original two-sided stratum comparisons imply
    equality of the actual tangent cones of psi restricted to
    R_i and H^m restricted to R_i at EVERY base point. *)
Theorem structure_density_stratum_tangent_agreement (R:realType) n m
    (psi:set (inner_metric_space (@euclidean_inner_productP R n))->\bar R)
    (F:set (inner_metric_space (@euclidean_inner_productP R n))) (b:R)
    (a:inner_metric_space (@euclidean_inner_productP R n)):
  is_measure psi ->is_borel_regular_measure psi ->psi setT< +oo ->(0<b)%R ->
  let S:=structure_rectifiable_density_stratum m psi F b in
  measure_approximate_tangent_cone (inner_norm_real_norm (@euclidean_inner_productP R n))
    (measure_restrict psi S) m a=
  measure_approximate_tangent_cone (inner_norm_real_norm (@euclidean_inner_productP R n))
    (measure_restrict (@hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R n)) m) S) m a.
Proof.
move=>hPsi hRegular hFinite hb S.
pose X:=inner_metric_space (@euclidean_inner_productP R n).
pose H:=@hausdorff_measure R [the metricType R of X] m.
have hH:=@hausdorff_measure_is_measure R [the metricType R of X] m.
have hFactor:(0<2^+m*b)%R by apply:mulr_gt0; rewrite ?exprn_gt0 // ltr0n.
apply:(@comparable_measure_approximate_tangents R (R_n R n)
  (inner_norm (@euclidean_inner_productP R n)) (inner_norm_real_norm (@euclidean_inner_productP R n)) m
  (measure_restrict psi S) (measure_restrict H S) a (2^+m*b)%R b
  (measure_restrict_is_measure hPsi S) (measure_restrict_is_measure hH S) hFactor hb).
- move=>A; exact:(@structure_rectifiable_density_stratum_comparisons R [the metricType R of X] m
    psi F (S `&` A) b hPsi hRegular hFinite hb (fun x hx=>hx.1)).2.
- move=>A.
  have hLow x:(S `&` A) x ->b^-1%R%:E<upper_metric_density m psi x.
    move=>[[hF hBand] _]; exact:(andP hBand).1.
  have hInv:(0<b^-1)%R by rewrite invr_gt0.
  have hBound:=@finite_upper_density_hausdorff_bound R [the metricType R of X] m psi (S `&` A)
    b^-1%R hPsi hRegular hFinite hInv hLow.
  by rewrite invrK in hBound.
Qed.

(** Source for [structure_density_stratum_tangent_plane]: the
    actual 3.2.19 appeal and BOTH tangent equalities in Federer
    3.3.18, p. 301. The original stratum is a Borel subset of
    an actual bounded rectifiable F; its finite Hausdorff mass is
    derived. Transfer the actual Hausdorff exceptional set with
    the proved original stratum comparison. The original omitted
    density is zero by actual 2.10.19(4), giving locality of the
    full-density test sets. No tangent or density assertion is
    supplied by the caller. *)
Theorem structure_density_stratum_tangent_plane (R:realType) n m
    (psi:set (inner_metric_space (@euclidean_inner_productP R n))->\bar R)
    (F:set (inner_metric_space (@euclidean_inner_productP R n))) (b:R):
  is_measure psi ->is_borel_regular_measure psi ->psi setT< +oo ->(0<b)%R ->
  borel_set F ->is_m_rectifiable m F ->
  measure_almost_everywhere_on psi (structure_rectifiable_density_stratum m psi F b)
    [set a|is_m_dimensional_approximate_tangent m psi a].
Proof.
move=>hPsi hRegular hFinite hb hF hRect.
pose X:=inner_metric_space (@euclidean_inner_productP R n).
pose H:=@hausdorff_measure R [the metricType R of X] m.
pose S:=structure_rectifiable_density_stratum m psi F b.
have hH:=@hausdorff_measure_is_measure R [the metricType R of X] m.
have hS:borel_set S:=@structure_rectifiable_density_stratum_borel R [the metricType R of X] m psi F b hPsi hF.
have hSRect:is_m_rectifiable m S.
  apply:(@rectifiable_subset R [the metricType R of X] m F S _ hRect).
  by move=>x [hx _].
have hRectH:=rectifiable_hausdorff_measure_rectifiable hSRect.
have hMeasH:=borel_regular_borel_measurable hH (@hausdorff_measure_borel_regular R [the metricType R of X] m) hS.
have hHPlanes:=(@federer_3_2_19 R m n S hRectH hMeasH).1.
pose GoodH:=[set a:X|
  partial_function_graph (metric_density m (measure_restrict H S)) a 1%E /\
  is_m_dimensional_approximate_tangent m (measure_restrict H S) a].
have hBadH:psi (S `\` GoodH)= 0.
  have hBound:=(@structure_rectifiable_density_stratum_comparisons R [the metricType R of X] m
    psi F (S `\` GoodH) b hPsi hRegular hFinite hb (fun x hx=>hx.1)).2.
  rewrite hHPlanes mule0 in hBound.
  apply/eqP; by rewrite eq_le hBound (measure_nonnegative hPsi).
pose GoodLoss:=[set a:X|partial_function_graph (metric_density m (measure_restrict psi (~` S))) a 0%E].
have hLoss:psi (S `\` GoodLoss)= 0:=
  @structure_density_stratum_omitted_density_zero R [the metricType R of X] m psi F b hPsi hRegular hFinite hb hF.
have hWhole:measure_restrict psi setT=psi by apply:funext=>A; rewrite /measure_restrict setTI.
have hCover:S `\` [set a|is_m_dimensional_approximate_tangent m psi a] `<=`
    (S `\` GoodH) `|` (S `\` GoodLoss).
  move=>a [hSA hn].
  have [hGH|hNotH]:=pselect (GoodH a); last by left; split.
  have [hGL|hNotLoss]:=pselect (GoodLoss a); last by right; split.
  exfalso; apply:hn.
  have hLocal:=@restricted_approximate_tangent_equal R (R_n R n)
    (inner_norm (@euclidean_inner_productP R n)) (inner_norm_real_norm (@euclidean_inner_productP R n)) m
    psi S setT a hPsi (subsetT S).
  rewrite setTD hWhole in hLocal.
  have hEqual:=hLocal hGL.
  have hComparable:=@structure_density_stratum_tangent_agreement R n m psi F b a hPsi hRegular hFinite hb.
  have [T hT]:=hGH.2.
  exists T; rewrite -hEqual hComparable; exact:hT.
have hUnionNull:=measure_null_union hPsi hBadH hLoss.
exact:(measure_null_subset hPsi hCover hUnionNull).
Qed.
