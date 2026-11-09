(** Federer (1969), 3.3.18, p. 301: the complete
    positive-density and tangent assertions for the ORIGINAL source. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations GrassmannSubspaces ModuleQuotient EuclideanInnerProduct InnerNorm InnerMetric
  HilbertFormCompactness InnerOwnNormTopology StructureConeUP StructureCone StructureFiniteSourceRegularisation
  StructureRectifiablePositiveDensity CountablyRectifiableFiniteDensityTangents
  BorelTestMeasureTangents ApproximateTangentNormalPlane ApproximateNormalConeZeroDensity
  RectifiableSetUP RectifiableTangentPlaneUP MeasureApproximateTangentUP MeasureApproximateNormalUP
  MeasureUP MeasureBasic MeasureRestriction MeasureAlmostUP MeasureAlmostBasic
  MeasureDerivationContext TopologicalBorel PartialFunctionUP MetricDensities.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [structure_measure_rectifiable_tangent_point]: the
    complete pointwise conclusion of Federer 3.3.18, p. 301.
    The ORIGINAL approximate tangent is an m-plane. Its actual
    polar normal is an (n-m)-plane, and for EVERY 0<s<1 the
    ORIGINAL cone about that normal has ordinary zero m-density.
    This is a conclusion predicate, not an added hypothesis. *)
Definition structure_measure_rectifiable_tangent_point (R:realType) n m
    (mu:set (inner_metric_space (@euclidean_inner_productP R n))->\bar R)
    (a:inner_metric_space (@euclidean_inner_productP R n)):Prop:=
  is_m_dimensional_approximate_tangent m mu a /\
  exists N:G (R_n R n) (n-m),
    (forall u,grassmann_val N u <->measure_approximate_normal_cone (@euclidean_inner_productP R n) mu m a u) /\
    forall s:R,(0<s<1)%R ->partial_function_graph (metric_density m
      (measure_restrict mu (structure_cone N a +oo s))) a 0.

(** Source for [federer_3_3_18]: BOTH original rectifiable-set
    assertions of Federer 3.3.18, p. 301. Original finite-mass
    (phi,m) rectifiable E has positive ORIGINAL restricted upper
    density almost everywhere. Under exactly the printed almost-
    everywhere finite-density hypothesis, the actual original
    tangent and normal and EVERY original aperture have the full
    displayed conclusion. Source measurability, density fields,
    tangent planes, comparison constants and regularisations are
    all derived or local, never extra theorem premises. *)
Theorem federer_3_3_18 (R:realType) n m (hmn:(m<=n)%N)
    (phi:set (inner_metric_space (@euclidean_inner_productP R n))->\bar R)
    (E:set (inner_metric_space (@euclidean_inner_productP R n))):
  is_structure_measure phi ->is_measure_m_rectifiable phi m E ->
  measure_almost_everywhere_on phi E [set a|0<upper_metric_density m (measure_restrict phi E) a] /\
  (measure_almost_everywhere_on phi E [set a|upper_metric_density m (measure_restrict phi E) a< +oo] ->
    measure_almost_everywhere_on phi E [set a|
      structure_measure_rectifiable_tangent_point m (measure_restrict phi E) a]).
Proof.
move=>hStructure hRect; split; first exact:federer_3_3_18_positive_density hStructure hRect.
move=>hFiniteDensity.
have [[hPhi [S [hS hLoss]]] hFinite]:=hRect.
pose X:=inner_metric_space (@euclidean_inner_productP R n).
pose mu:=measure_restrict phi E.
have hMu:is_measure mu:=measure_restrict_is_measure hPhi E.
have [psi [hReg [hClass [hRadon [hTotal [hValue [hDomination hDensity]]]]]]]:=
  @structure_finite_source_regularisation R n m phi E hStructure hFinite.
have hPsi:=derivation_measure_law hClass.
have hRegular:=derivation_measure_borel_regular hClass.
have hWholeFinite:psi setT< +oo by rewrite hTotal.
pose Good:=[set a:X|upper_metric_density m psi a< +oo ->is_m_dimensional_approximate_tangent m psi a].
have hStrataNull:psi (S `\` Good)= 0:=
  @countably_rectifiable_finite_density_tangents R n m psi S hPsi hRegular hWholeFinite hS.
have hOriginalNull:phi (E `&` (S `\` Good))= 0.
  have hBound:=hDomination (S `\` Good); rewrite hStrataNull in hBound.
  apply/eqP; rewrite eq_le (measure_nonnegative hPhi) andbT; exact:hBound.
have hTangentAgreement a:
    measure_approximate_tangent_cone (inner_norm_real_norm (@euclidean_inner_productP R n)) psi m a=
    measure_approximate_tangent_cone (inner_norm_real_norm (@euclidean_inner_productP R n)) mu m a.
  apply:(@borel_test_measure_approximate_tangents R (R_n R n)
    (inner_norm (@euclidean_inner_productP R n)) (inner_norm_real_norm (@euclidean_inner_productP R n))
    m psi mu a hPsi hMu).
  move=>B hB; apply:hValue.
  exact:(@inner_own_norm_borel_iff R (R_n R n) (@euclidean_inner_product R n)
    (@euclidean_inner_productP R n) B).2 hB.
have hData a:upper_metric_density m mu a< +oo ->Good a ->
    structure_measure_rectifiable_tangent_point m mu a.
  move=>hFiniteAt hGood.
  have hPsiFinite:upper_metric_density m psi a< +oo by rewrite hDensity.
  have hPsiPlane:=hGood hPsiFinite.
  have hMuPlane:is_m_dimensional_approximate_tangent m mu a.
    have [T hT]:=hPsiPlane; exists T; rewrite -(hTangentAgreement a); exact:hT.
  split; first exact:hMuPlane.
  have [N hN]:=@approximate_tangent_normal_plane_exists R n m hmn mu a hMuPlane.
  exists N; split; first exact:hN.
  move=>s hs; exact:(@approximate_normal_cone_zero_density R n m (n-m) mu a N s hMu hMuPlane hN hs).
pose Finite:=[set a:X|upper_metric_density m mu a< +oo].
pose Target:=[set a:X|structure_measure_rectifiable_tangent_point m mu a].
have hCover:E `\` Target `<=` (E `\` Finite) `|` ((E `\` S) `|` (E `&` (S `\` Good))).
  move=>a [ha hn].
  have [hFiniteAt|hNotFinite]:=pselect (Finite a); last by left; split.
  right.
  have [hInS|hNotS]:=pselect (S a); last by left; split.
  right; split; first exact:ha.
  split; first exact:hInS.
  by move=>hGood; apply:hn; exact:hData a hFiniteAt hGood.
have hRestNull:=measure_null_union hPhi hLoss hOriginalNull.
have hAllNull:=measure_null_union hPhi hFiniteDensity hRestNull.
exact:(@measure_null_subset R [the choiceType of X] phi hPhi (E `\` Target)
  ((E `\` Finite) `|` ((E `\` S) `|` (E `&` (S `\` Good)))) hCover hAllNull).
Qed.
