(** Federer (1969), 3.4.7, p. 324: the
    original hypothesis of 3.4.6 holds for almost
    all directions, both in ambient space and on
    its unit sphere. The two actual null exceptional
    sets prove this consequence without a measurable
    source or a chosen good-direction hypothesis. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals
  constructive_ereal topology.
From Federer Require Import Hom RealNormUP GrassmannAbbreviations EuclideanInnerProduct InnerNorm InnerMetric
  HilbertFormCompactness ContinuousMultilinearUP ContinuousMultilinearSealed AnalyticGermUP
  AnalyticGermJetsSealed AnalyticGermDirectionalOrderUP EuclideanAnalyticDirections
  EuclideanLebesgueDimensions HausdorffMeasure MeasureAlmostUP MeasureAlmostBasic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [euclidean_first_jet_directions_almost_regular]:
    the final sentence of the first paragraph of
    3.4.7, p. 324. The original finite
    first nonzero order is positive; all lower
    actual derivatives vanish at the original centre.
    The corresponding directional order holds almost
    everywhere for both original measures. *)
Theorem euclidean_first_jet_directions_almost_regular (R:realType) n
    (a:R_n R n) k
    (alpha:analytic_germ_space (inner_norm_real_norm (@euclidean_inner_productP R n)) a):
  let NX:=inner_norm (@euclidean_inner_productP R n) in
  let hNX:=inner_norm_real_norm (@euclidean_inner_productP R n) in
  (0<k)%N ->
  (forall i,(i<k)%N ->@AnalyticGermJets.value R (R_n R n) NX hNX a i alpha = 0) ->
  @AnalyticGermJets.value R (R_n R n) NX hNX a k alpha<>0 ->
  measure_almost_everywhere (@euclidean_lebesgue_measure R n)
    [set v|is_analytic_germ_direction_regular_at alpha k v] /\
  measure_almost_everywhere_on
    (@hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R n)) (n-1))
    [set v|NX v = 1] [set v|is_analytic_germ_direction_regular_at alpha k v].
Proof.
move=>NX hNX hPositive hLower hTop.
pose X:=inner_metric_space (@euclidean_inner_productP R n).
pose diagonal:=fun v:R_n R n=>@ContinuousMultilinear.evaluation R k (R_n R n) R^o
  NX (fun t=>`|t|) hNX (@scalar_absolute_value_norm R) [ffun _:'I_k=>v]
    (@AnalyticGermJets.value R (R_n R n) NX hNX a k alpha).
pose Good:set X:=fun v=>is_analytic_germ_direction_regular_at alpha k v.
have hGood v:diagonal v<>0 ->Good v.
  move=>hNonzero;split;first exact:hPositive.
  split;last exact:hNonzero.
  move=>i hi;by rewrite (hLower i hi) linear0.
have hBad v:~Good v ->diagonal v = 0.
  move=>hNotGood;apply:contrapT=>hNonzero;apply:hNotGood;exact:hGood v hNonzero.
have [hAmbient hSphere]:=@euclidean_analytic_germ_exceptional_directions_null R n a k alpha hTop.
split.
- apply:(@measure_null_subset R (Choice.clone X _) (@euclidean_lebesgue_measure R n)
    (euclidean_lebesgue_is_measure R n) (~` Good) [set v|diagonal v = 0]);last exact:hAmbient.
  move=>v hv;exact:hBad v hv.
- apply:(@measure_null_subset R (Choice.clone X _)
    (@hausdorff_measure R X (n-1)) (@hausdorff_measure_is_measure R X (n-1))
    ([set v|NX v = 1] `\` Good) [set v|diagonal v = 0 /\NX v = 1]);last exact:hSphere.
  move=>v hv;split;[exact:hBad v hv.2|exact:hv.1].
Qed.
