(** Federer (1969), 3.2.47(3), p. 283, first
    proof paragraph: apply 3.2.22(2) to H_e and
    map a good fibre by Phi. The positive actual
    isotropy mass supplies a good fibre. This supporting
    lemma isolates that measure argument, retaining arbitrary E. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp
  classical_sets constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric
  MeasureUP MeasureAlmostUP MeasureBasic MeasureAlmostBasic
  RectifiableSetUP RectifiableCoareaFibres MappingMultiplicity
  LipschitzUP LipschitzBasic FiniteMeasureRectifiableImages
  MeasureRectifiableSubset HausdorffMeasure.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [positive_measure_almost_point]: the positive
    mass of I permits selecting a good fibre in
    the converse proof of 3.2.47(3), p. 283.
    This is an elementary consequence of 2.3.1, p. 72. *)
Lemma positive_measure_almost_point (R:realType) (X:choiceType)
    (nu:set X->\bar R) (hNu:is_measure nu) (Z P:set X):
  0<nu Z ->measure_almost_everywhere nu P ->exists z,Z z /\P z.
Proof.
move=>hPositive hAlmost.
case:(pselect (exists z,Z z /\P z))=>hExists; first exact hExists.
have hSubset:Z `<=` ~`P.
  move=>z hz hp; apply:hExists; exists z; by split.
have hZero:=@measure_null_subset R X nu hNu Z (~`P) hSubset hAlmost.
by rewrite hZero ltxx in hPositive.
Qed.

(** Source for [rectifiable_fibre_image_converse]: supporting
    use of 3.2.22(2), p. 258, in the first
    conclusion of 3.2.47(3), p. 283. A positive-mass
    family of complete fibres covers the original E under
    its actual Lipschitz image map. Source and slicing-target
    rectifiability are discharged separately in the application. *)
Theorem rectifiable_fibre_image_converse (R:realType) r mu n v t
    (W:set (R_n R n)) (Z:set (R_n R v)) (E:set (R_n R t))
    (F:inner_metric_space (@euclidean_inner_productP R n)->
      inner_metric_space (@euclidean_inner_productP R v))
    (P:inner_metric_space (@euclidean_inner_productP R n)->
      inner_metric_space (@euclidean_inner_productP R t)):
  is_measure_m_rectifiable (@hausdorff_measure R
    (inner_metric_space (@euclidean_inner_productP R n)) (r+mu)) (r+mu)%N W ->
  measure_measurable (@hausdorff_measure R
    (inner_metric_space (@euclidean_inner_productP R n)) (r+mu)) W ->
  is_measure_m_rectifiable (@hausdorff_measure R
    (inner_metric_space (@euclidean_inner_productP R v)) mu) mu Z ->
  measure_measurable (@hausdorff_measure R
    (inner_metric_space (@euclidean_inner_productP R v)) mu) Z ->
  0<@hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R v)) mu Z ->
  is_metric_lipschitz setT F ->(forall w,W w ->Z (F w)) ->
  is_metric_lipschitz setT P ->
  (forall z,Z z ->E `<=` P @` mapping_fibre F W z) ->
  is_measure_m_rectifiable (@hausdorff_measure R
    (inner_metric_space (@euclidean_inner_productP R t)) r) r E.
Proof.
move=>hWRect hW hZRect hZ hPositive hF hRange hP hCover.
have hDim:(mu<=r+mu)%N by rewrite leq_addl.
have hFibres:=@rectifiable_coarea_fibres R (r+mu)%N n mu v W Z F
  hDim hWRect hW hZRect hZ hF hRange.
rewrite addnK in hFibres.
have [z [hz [hRect hMeas]]]:=@positive_measure_almost_point R
  (inner_metric_space (@euclidean_inner_productP R v))
  (@hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R v)) mu)
  (@hausdorff_measure_is_measure R (inner_metric_space (@euclidean_inner_productP R v)) mu)
  Z _ hPositive hFibres.
have hRestricted:is_metric_lipschitz (mapping_fibre F W z) P.
  have [L [hL hBound]]:=hP; exists L; split; first exact hL.
  exact:metric_lipschitz_bound_restrict (fun x _=>I) hBound.
have hImage:=hausdorff_measure_rectifiable_lipschitz_image hRestricted hRect.
exact (@measure_rectifiable_subset R (inner_metric_space (@euclidean_inner_productP R t))
  (@hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R t)) r) r
  (P @` mapping_fibre F W z) E (hCover z hz) hImage).
Qed.
