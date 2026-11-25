(** Federer (1969), 3.2.23, p. 260: the whole measure identity
    on a pair of injective image pieces. Compact charts of 3.2.18
    refine the printed decomposition through 3.2.4. Borel traces
    retain the exact product Jacobian and area calculation. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric
  EuclideanBlockCoordinates EuclideanCartesianMap EuclideanCartesianBorel RectifiableCompactChartsUP
  RectifiableCompactChartLaws RectifiableBorelChartTrace LipschitzBasic CompactLipschitzImageMass
  CompactCartesianAreaMass HausdorffMeasure HausdorffClosedCoverAgreement
  EuclideanLebesgueHaar MeasureUP MeasureRestriction MeasurePushforward
  BorelRegularMeasureUP BorelRegularRestriction BorelRegularHomeomorphicPushforward
  TopologicalBorel CountableOpenBaseUP FiniteBorelProductIdentification FiniteBorelProductRestriction ProductMeasure.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [compact_chart_product_measure]: the local full
    restricted-measure identity underlying Federer 3.2.23, p. 260.
    The conclusion holds on every test subset, not just rectangles.
    The usual coordinate split transports H^(m+mu) restricted to
    psi(K) times gamma(C) to the product of their Hausdorff
    restrictions. Zero-dimensional blocks and empty pieces are retained. *)
Theorem compact_chart_product_measure (R:realType) m mu n v (lambda kappa:R)
    (K:set (R_n R m)) (C:set (R_n R mu))
    (psi:R_n R m->R_n R n) (gamma:R_n R mu->R_n R v):
  is_uniform_compact_rectifiable_chart lambda K psi ->
  is_uniform_compact_rectifiable_chart kappa C gamma ->
  measure_pushforward (@euclidean_block_split R n v)
    (measure_restrict (@hausdorff_measure R
      (inner_metric_space (@euclidean_inner_productP R (n+v))) (m+mu))
      (euclidean_cartesian_set (psi @` K) (gamma @` C)))=
  product_measure
    (measure_restrict_is_measure (@hausdorff_measure_is_measure R
      (inner_metric_space (@euclidean_inner_productP R n)) m) (psi @` K))
    (measure_restrict_is_measure (@hausdorff_measure_is_measure R
      (inner_metric_space (@euclidean_inner_productP R v)) mu) (gamma @` C)).
Proof.
move=>hSource hTarget.
pose X:=inner_metric_space (@euclidean_inner_productP R n).
pose Y:=inner_metric_space (@euclidean_inner_productP R v).
pose T:=inner_metric_space (@euclidean_inner_productP R (n+v)).
pose H:=@hausdorff_measure R X m.
pose J:=@hausdorff_measure R Y mu.
pose L:=@hausdorff_measure R T (m+mu).
pose P:=psi @` K.
pose Q:=gamma @` C.
pose alpha:=measure_restrict H P.
pose beta:=measure_restrict J Q.
pose sigma:=measure_pushforward (@euclidean_block_split R n v)
  (measure_restrict L (euclidean_cartesian_set P Q)).
have hH:=@hausdorff_measure_is_measure R X m.
have hJ:=@hausdorff_measure_is_measure R Y mu.
have hL:=@hausdorff_measure_is_measure R T (m+mu).
have hP:@borel_set (inner_metric_space (@euclidean_inner_productP R n)) P.
  exact:(closed_borel_set (compact_closed (@metric_hausdorff R X)
    (uniform_compact_chart_image_compact hSource))).
have hQ:@borel_set (inner_metric_space (@euclidean_inner_productP R v)) Q.
  exact:(closed_borel_set (compact_closed (@metric_hausdorff R Y)
    (uniform_compact_chart_image_compact hTarget))).
have hAlpha:=measure_restrict_is_measure hH P.
have hBeta:=measure_restrict_is_measure hJ Q.
have hAlphaRegular:=borel_regular_restrict_borel hH (@hausdorff_measure_borel_regular R X m) hP.
have hBetaRegular:=borel_regular_restrict_borel hJ (@hausdorff_measure_borel_regular R Y mu) hQ.
have hRestrictedRegular:=borel_regular_restrict_borel hL
  (@hausdorff_measure_borel_regular R T (m+mu)) (euclidean_cartesian_borel hP hQ).
have hSigma:=measure_pushforward_is_measure (@euclidean_block_split R n v)
  (measure_restrict_is_measure hL (euclidean_cartesian_set P Q)).
have hSigmaRegular:=borel_regular_homeomorphic_pushforward
  (measure_restrict_is_measure hL (euclidean_cartesian_set P Q))
  (@euclidean_block_splitK R n v) (@euclidean_block_joinK R n v)
  (@euclidean_block_split_continuous R n v) (@euclidean_block_join_continuous R n v)
  hRestrictedRegular.
have hPsi:=metric_lipschitz_of_bound (rectifiable_chart_global_bound hSource).
have hGamma:=metric_lipschitz_of_bound (rectifiable_chart_global_bound hTarget).
have hAlphaFinite:alpha setT< +oo.
  rewrite /alpha /measure_restrict setIT.
  exact:(compact_lipschitz_image_finite_hausdorff_mass hPsi (rectifiable_chart_compact hSource)).
have hBetaFinite:beta setT< +oo.
  rewrite /beta /measure_restrict setIT.
  exact:(compact_lipschitz_image_finite_hausdorff_mass hGamma (rectifiable_chart_compact hTarget)).
have [U hU]:=euclidean_countable_open_base R n.
have [V hV]:=euclidean_countable_open_base R v.
have hBridge:=product_measure_factors_equal hAlpha
  (measure_restrict_is_measure (@hausdorff_measure_is_measure R X m) P)
  hBeta (measure_restrict_is_measure (@hausdorff_measure_is_measure R Y mu) Q)
  (erefl alpha) (erefl beta).
apply:(eq_trans _ hBridge).
change (sigma=product_measure hAlpha hBeta).
apply:(@finite_borel_rectangles_determine_product R
  (inner_metric_space (@euclidean_inner_productP R n))
  (inner_metric_space (@euclidean_inner_productP R v)) alpha beta hAlpha hBeta sigma U V
  hU hV hAlphaRegular hBetaRegular hSigma hSigmaRegular hAlphaFinite hBetaFinite)=>E F hE hF.
have [A [hA [_ [hImageA [hMassA hInjectA]]]]]:=uniform_compact_chart_borel_trace hSource hE.
have [B [hB [_ [hImageB [hMassB hInjectB]]]]]:=uniform_compact_chart_borel_trace hTarget hF.
have hArea:=euclidean_cartesian_injective_area_mass hPsi hGamma hA hB hInjectA hInjectB hMassA hMassB.
rewrite hImageA in hArea.
rewrite hImageB in hArea.
have hSet:(euclidean_cartesian_set P Q) `&`
    ((@euclidean_block_split R n v) @^-1` (E `*` F))=
    euclidean_cartesian_set (P `&` E) (Q `&` F).
  by apply/seteqP; split; move=>p [[h1 h2] [h3 h4]]; split; split.
rewrite /sigma /measure_pushforward /measure_restrict hSet.
exact hArea.
Qed.
