(** Federer (1969), 3.2.25, p. 261: the full
    measurable orientation lemma for an arbitrary (H^m,m)-
    rectifiable W. The proof's measurable-source reduction uses
    a genuine measure hull, not a null difference assertion.
    Erratum p. 5, book p. 261 line 4: H^m almost everywhere. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology.
From Federer Require Export RectifiableOrientationUP.
From Federer Require Import ModuleQuotient GrassmannAbbreviations EuclideanInnerProduct EuclideanLinearMaps
  InnerNorm InnerMetric HilbertFormCompactness InnerExteriorPositivity ExteriorGrading
  PartialFunctionUP PartialFunctionSourceRestriction MeasureUP MeasureBasic MeasureAlmostUP MeasureAlmostBasic
  MeasureRestriction MeasureHull BorelRegularMeasureUP HausdorffMeasure HausdorffClosedCoverAgreement
  RectifiableSetUP RectifiableTangentPlaneUP RectifiableBorelMeasureHull MeasureHullApproximateTangent
  RectifiableMeasurableOrientation BorelPartialGluing MeasurableFunctionUP MeasurableConullSourceRestriction
  InnerOwnNormTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [federer_3_2_25]: the complete orientation
    lemma in Federer 3.2.25, p. 261, with erratum
    p. 5 line 4. W need not be measurable. The
    field is H^m restricted-to-W measurable, has simple
    unit values everywhere on its actual domain, and has
    the exact associated m-dimensional approximate tangent
    plane almost everywhere on W. Its domain is contained
    in W; undefined exceptional points get no default value. *)
Theorem federer_3_2_25 (R:realType) m n (W:set (R_n R n)):
  is_measure_m_rectifiable (@hausdorff_measure R
    (inner_metric_space (@euclidean_inner_productP R n)) m) m W ->
  exists T:partial_function (R_n R n) (exterior_power (R_n R n) m),
    is_rectifiable_measurable_orientation W T /\partial_function_domain T `<=` W.
Proof.
move=>hRect.
pose X:=inner_metric_space (@euclidean_inner_productP R n).
pose H:=@hausdorff_measure R X m.
pose hNX:=inner_norm_real_norm (@euclidean_inner_productP R n).
have hH:=@hausdorff_measure_is_measure R X m.
have hRegular:=@hausdorff_measure_borel_regular R X m.
have [M [hMBorel [hHull hMRect]]]:=rectifiable_borel_measure_hull hRect.
have hWM:=measure_hull_subset hHull.
have hMMeas:=borel_regular_borel_measurable hH hRegular hMBorel.
have [T0 [hT0Borel hT0]]:=rectifiable_measurable_orientation_borel hMRect hMMeas.
have hDomainM:H (M `\` partial_function_domain T0)=0.
  exact:measurable_function_domain (rectifiable_orientation_measurable hT0).
have hDomainW:H (W `\` partial_function_domain T0)=0.
  apply:(measure_null_subset hH _ hDomainM)=>w [hw hn]; split; first exact:hWM w hw.
  exact hn.
have hMeasOnW:=borel_partial_measurable_on hH hRegular hT0Borel hDomainW.
pose T:=partial_function_source_restrict W T0.
have hWConull:measure_almost_everywhere (measure_restrict H W) W.
  rewrite /measure_almost_everywhere /measure_restrict -setDE setDv.
  exact:measure_empty hH.
have hCone w:=@measure_hull_approximate_tangent R (R_n R n)
  (inner_norm (@euclidean_inner_productP R n)) hNX H m W M w hH
  (fun A hA=>borel_regular_borel_measurable hH hRegular
    ((inner_own_norm_borel_iff (@euclidean_inner_productP R n) A).2 hA)) hHull.
exists T; split.
- constructor.
  + exact:(measurable_conull_source_restriction (measure_restrict_is_measure hH W) hWConull hMeasOnW).
  + move=>w xi [hw hGraph]; exact:(rectifiable_orientation_unit_simple hT0 hGraph).
  + apply:(measure_null_subset hH _ (rectifiable_orientation_tangent hT0))=>w [hw hNot].
    split; first exact:hWM w hw.
    move=>[xi [hGraph [hTangent hPlane]]]; apply:hNot.
    exists xi; split; first by split.
    split; first exact:(eq_trans (hCone w) hTangent).
    have [P hP]:=hPlane; exists P; rewrite (hCone w); exact hP.
- move=>w [xi [hw _]]; exact hw.
Qed.
