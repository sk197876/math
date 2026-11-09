(** Federer (1969), 3.3.20, p. 306:
    closed sets with null original coordinate images are purely unrectifiable. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric ExteriorIndices
  CoordinateProjection EuclideanLebesgueDimensions RectifiableSetUP RectifiableClosure
  RectifiableFiniteHausdorffMass RectifiableNullCoordinateImages MeasureUP MeasureBasic
  MeasureAlmostBasic HausdorffMeasure HausdorffClosedCoverAgreement BorelRegularMeasureUP
  TopologicalBorel.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [closed_null_coordinate_images_pure]: supporting
    pure unrectifiability argument in 3.3.20,
    p. 306. An arbitrary rectifiable test
    subset may be replaced by its actual closure,
    still inside the original closed set. This
    proves the measurability needed by the corrected
    3.2.27; the original test need not be
    measurable. No finite mass premise on E
    or null nonmeasurable hull difference is assumed. *)
Theorem closed_null_coordinate_images_pure (R:realType) m n
    (hmn:(m<=n)%N) (E:set (R_n R n)):
  closed (E:set (inner_metric_space (@euclidean_inner_productP R n))) ->
  (forall lambda:Lambda n m,euclidean_lebesgue_measure m
    ((@coordinate_projection R n m lambda) @` E)=0) ->
  is_purely_measure_m_unrectifiable (@hausdorff_measure R
    (inner_metric_space (@euclidean_inner_productP R n)) m) m E.
Proof.
move=>hClosed hImages.
pose X:metricType R:=[the metricType R of inner_metric_space (@euclidean_inner_productP R n)].
pose mu:=@hausdorff_measure R X m.
have hMu:=@hausdorff_measure_is_measure R X m.
split=>//;move=>[F [hFE [hRect hPositive]]].
pose K:=closure (F:set X).
have hKE:K `<=` E.
  have hMonotone:K `<=` closure (E:set X):=@closureS X F E hFE.
  by rewrite -((@closure_id X (E:set X)).1 hClosed) in hMonotone.
have hKR:is_m_rectifiable m K:=rectifiable_closure hRect.
have hKMeas:measure_measurable mu K.
  apply:(borel_regular_borel_measurable hMu (hausdorff_measure_borel_regular _ _)).
  exact:closed_borel_set (@closed_closure X F).
have hKImages lambda:euclidean_lebesgue_measure m ((@coordinate_projection R n m lambda) @` K)=0.
  apply:(@measure_null_subset R [the choiceType of inner_metric_space (@euclidean_inner_productP R m)]
    (@euclidean_lebesgue_measure R m) (euclidean_lebesgue_is_measure R m)
    _ _ _ (hImages lambda)).
  move=>y [x hx hValue];exists x;first exact:hKE x hx.
  exact:hValue.
have hZero:=@rectifiable_null_coordinate_images_mass_zero R m n hmn K
  (rectifiable_hausdorff_measure_rectifiable hKR) hKMeas hKImages.
have hBound:=measure_mono hMu (@subset_closure X F).
rewrite hZero in hBound.
by have:=lt_le_trans hPositive hBound;rewrite ltxx.
Qed.
