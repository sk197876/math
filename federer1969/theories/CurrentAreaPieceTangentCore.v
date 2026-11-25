(** Federer (1969), 4.1.25, p. 383: identify
    the range of every actual injective differential
    with the approximate tangent of the original compact
    image. Follow the printed use of 3.2.2,
    3.2.17 and 2.10.19(4). This supporting step treats
    one original piece; countable assembly is separate. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals constructive_ereal topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP
  NormDifferentialDirectional GrassmannAbbreviations EuclideanInnerProduct
  InnerNorm InnerMetric HilbertFormCompactness InnerOwnNormTopology
  EuclideanLebesgueDimensions EuclideanHausdorffLebesgue EuclideanFullDensityCore
  MeasureUP MeasureBasic MeasureAlmostUP MeasureAlmostBasic MeasureRestriction
  MeasureFiniteClosure BorelRegularMeasureUP TopologicalBorel
  HausdorffMeasure HausdorffClosedCoverAgreement NullLipschitzArea
  LipschitzUP LipschitzBasic LipschitzMeasurableImages
  MetricBiLipschitzUP EuclideanBiLipschitzTangentPlanes
  InjectiveDifferentialPieceUP InjectivePieceBiLipschitz
  CompactLipschitzImageMass FiniteMeasurableTangentRestriction
  MeasureApproximateTangentUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.
Section AreaPieceTangent.
Variable R : realType.
Variables m n : nat.
Local Notation X := (inner_metric_space (@euclidean_inner_productP R m)).
Local Notation Y := (inner_metric_space (@euclidean_inner_productP R n)).
Local Notation NX := (inner_norm (@euclidean_inner_productP R m)).
Local Notation NY := (inner_norm (@euclidean_inner_productP R n)).
Local Notation hNX := (inner_norm_real_norm (@euclidean_inner_productP R m)).
Local Notation hNY := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation mu := (@euclidean_lebesgue_measure R m).
Local Notation H := (@hausdorff_measure R Y m).
Variable f : X -> Y.
Variable K : set X.
Hypothesis hLip : is_metric_lipschitz setT f.
Hypothesis hK : compact K.
Local Notation W := (f @` K).

(** Source for [current_area_piece_tangent_core]: the
    full-density source core and common target plane
    for one piece in Federer 4.1.25, p. 383.
    Only a null source subset and its null image
    are removed. The final target assertion quantifies
    over every original differential at every retained
    source point in that full fibre. *)
Theorem current_area_piece_tangent_core (lambda : R) (E : set X) :
  is_injective_differential_piece f lambda E ->
  exists S : set X,
    S `<=` E `&` K /\ mu ((E `&` K) `\` S) = 0 /\
    H (f @` ((E `&` K) `\` S)) = 0 /\
    measure_almost_everywhere H [set y | forall x, S x -> f x = y ->
      forall D : Hom (R_n R m) (R_n R n),
        has_norm_differential NX NY setT f x D ->
        measure_approximate_tangent_cone hNY (measure_restrict H W) m y = range D].
Proof.
move=> hPiece.
have hMu := euclidean_lebesgue_is_measure R m.
have hH := @hausdorff_measure_is_measure R Y m.
have hEBorel : @borel_set X E := (inner_own_norm_borel_iff _ E).2 hPiece.1.
have hEMeas : measure_measurable mu E := borel_regular_borel_measurable
  hMu (euclidean_lebesgue_borel_regular R m) hEBorel.
have hKMeas : measure_measurable mu K := borel_regular_borel_measurable
  hMu (euclidean_lebesgue_borel_regular R m)
  (closed_borel_set (compact_closed (@metric_hausdorff R X) hK)).
have hA : measure_measurable mu (E `&` K) :=
  measure_measurable_intersection hMu hEMeas hKMeas.
have [S [hS [hLoss hDensity]]] := euclidean_full_density_core_exists hA.
have hSMeas : measure_measurable mu S.
  have hSet : S = (E `&` K) `\` ((E `&` K) `\` S).
    apply/seteqP; split.
    - move=> x hx; split; first exact: hS x hx.
      by move=> [_ hn]; exact: hn hx.
    - move=> x [hx hNot]; apply: contrapT => hOutside.
      apply: hNot; by split.
  rewrite hSet; apply: measure_measurable_difference;
    [exact: hMu | exact: hA | apply: measure_null_measurable; [exact: hMu | exact: hLoss]].
have hImageNull : H (f @` ((E `&` K) `\` S)) = 0.
  have hSourceNull : @hausdorff_measure R X m ((E `&` K) `\` S) = 0.
    by rewrite (euclidean_hausdorff_spherical_lebesgue _).1.
  have [L [hL hBound]] := hLip.
  exact: null_hausdorff_lipschitz_image hBound hSourceNull.
have [L [hL hBi]] := injective_piece_bilipschitz_bound hPiece.
have hSBi : @is_metric_bilipschitz_bound R X Y S f L.
  split.
  - exact: metric_lipschitz_bound_restrict (fun x hx => (hS x hx).1) hBi.1.
  - move=> x y hx hy; exact: hBi.2 x y (hS x hx).1 (hS y hy).1.
have hImageMeas := euclidean_lipschitz_measurable_image hLip hSMeas.
have hWMeas := euclidean_lipschitz_measurable_image hLip hKMeas.
have hImageSubset : f @` S `<=` W.
  move=> y [x hx <-]; exists x; first exact: (hS x hx).2.
  reflexivity.
have hPlane := finite_measurable_subset_approximate_tangent_equal
  hWMeas hImageMeas hImageSubset (compact_lipschitz_image_finite_hausdorff_mass hLip hK).
have hAlmost := (measure_almost_everywhere_on_implication _ _ _).1 hPlane.
exists S; split; first exact: hS.
split; first exact: hLoss.
split; first exact: hImageNull.
apply: (measure_almost_everywhere_mono hH _ hAlmost) => y hAt x hx hXY D hD.
have hAtImage : (f @` S) y by exists x.
have hEqual := hAt hAtImage.
have [D0 [hD0 hInjective]] := hPiece.2.1 x (hS x hx).1.
have hDEqual : D = D0 := norm_differential_unique hNX hNY hD hD0.
have hDInjective : injective D by rewrite hDEqual.
have hImagePlane := euclidean_bilipschitz_tangent_planes hSBi hL hx
  hDInjective hD (hDensity x hx).
rewrite hXY in hImagePlane.
exact: eq_trans (esym hEqual) (eq_trans hImagePlane.1 hImagePlane.2).
Qed.
End AreaPieceTangent.
