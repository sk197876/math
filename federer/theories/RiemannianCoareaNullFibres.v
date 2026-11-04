(** Federer (1969), 3.2.46, p. 282: the
    null-source fibre reduction for actual Riemannian metrics.
    The original coordinate extensions, ordinary null coarea
    and a countable open cover prove it. No coarea identity
    or integrability conclusion is assumed in this step. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp
  classical_sets constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric
  EuclideanLebesgueDimensions RiemannianTensorUP RiemannianMetricCarrier
  RiemannianHausdorff RiemannianPathLipschitz RiemannianChartReference
  RiemannianVolumeCompletion RiemannianVolumeConullCoordinates RiemannianHausdorffNullEquivalence
  RealHausdorffMeasure MappingMultiplicity LipschitzUP CoareaNullSourceAgreement
  MeasureUP MeasureAlmostUP MeasureAlmostBasic MeasureNullModification
  MeasureLocalFibreNullTransfer ContinuousBorelPreimages.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [riemannian_coarea_null_source_fibres]:
    the null-source case of 3.2.11, p. 249,
    extended by 3.2.46, p. 282. Every original
    Riemannian-volume null set has H_rho^(m-n)-null
    fibres at almost every original target point, for
    all n<=m, including n=0. No source measurability,
    boundedness, finite distance or rank premise is added. *)
Theorem riemannian_coarea_null_source_fibres (R : realType) m n A B g h
    (hg : @is_continuous_riemannian_tensor R m A g)
    (hh : @is_continuous_riemannian_tensor R n B h)
    (f : riemannian_metric_space hg -> riemannian_metric_space hh)
    (hpSource : 0<=m%:R :> R) (hpTarget : 0<=n%:R :> R)
    (hpFibre : 0<=(m-n)%:R :> R) :
  (n<=m)%N -> is_riemannian_path_lipschitz f ->
  forall N, riemannian_hausdorff_measure hg m%:R hpSource N=0%E ->
    measure_almost_everywhere (riemannian_hausdorff_measure hh n%:R hpTarget)
      [set y | riemannian_hausdorff_measure hg (m-n)%:R hpFibre (mapping_fibre f N y)=0%E].
Proof.
move=> hnm hLip.
pose X := [the topologicalType of riemannian_metric_space hg].
pose Y := [the choiceType of riemannian_metric_space hh].
pose E := [the topologicalType of inner_metric_space (@euclidean_inner_productP R m)].
pose mu := riemannian_hausdorff_measure hg m%:R hpSource.
pose sigma := riemannian_hausdorff_measure hg (m-n)%:R hpFibre.
pose beta := riemannian_hausdorff_measure hh n%:R hpTarget.
have hMu := @riemannian_hausdorff_is_measure R m A g hg m%:R hpSource.
have hSigma := @riemannian_hausdorff_is_measure R m A g hg (m-n)%:R hpFibre.
have hBeta := @riemannian_hausdorff_is_measure R n B h hh n%:R hpTarget.
have [C hBase] := @riemannian_chart_countable_open_base R m A g hg.
apply:(@measure_local_fibre_null_transfer R X Y mu sigma beta f C hMu hSigma hBeta hBase).
move=> a.
have [U [K [F [hU [hUa [hUA [hK [hBound [hRange hAgree]]]]]]]]] :=
  @riemannian_path_map_local_coordinates R m n A B g h hg hh f hLip a.
pose V : set X := (fun x : X=>(val x : E)) @^-1` U.
have hV : open V := @open_comp X E (fun x=>val x) U
  (fun x _=>@riemannian_chart_inclusion_continuous R m A g hg x) hU.
exists V; split; first exact hV; split; first exact hUa.
move=> N hNV hNull.
pose S := (fun x : X=>(val x : E)) @` N.
have hSourceNull : @euclidean_lebesgue_measure R m S=0%E.
  have hReference := (@riemannian_volume_reference_null_iff R m A g hg hpSource N).1 hNull.
  by rewrite riemannian_chart_reference_value in hReference.
have hFLip : is_metric_lipschitz setT F by exists K; split.
have hOrdinary := @coarea_null_source_fibres_zero R m n F S hnm hFLip hSourceNull.
have hActual := @riemannian_volume_conull_coordinate_preimage R n B h hh hpTarget
  [set z | @HausdorffMeasure.hausdorff_measure R
    (inner_metric_space (@euclidean_inner_productP R m)) (m-n) (mapping_fibre F S z)=0%E]
  hOrdinary.
apply:(@measure_almost_everywhere_mono R Y beta hBeta _ _ _ hActual)=> y hy.
apply:(@riemannian_hausdorff_null_iff R m A g hg (m-n)%:R hpFibre (mapping_fibre f N y)).2.
rewrite real_hausdorff_measure_natural.
have hImage : (fun x : X=>val x) @` mapping_fibre f N y=mapping_fibre F S (val y).
  apply/seteqP; split=> z.
  - move=> [x [hx hxy] <-]; split; first by exists x.
    by rewrite (hAgree x (hNV x hx)) hxy.
  - move=> [[x hx <-] hxy]; exists x; last by []; split; first exact hx.
    apply:val_inj; rewrite -(hAgree x (hNV x hx)); exact hxy.
by rewrite hImage.
Qed.

(** Source for [riemannian_coarea_null_source_fibre_agreement]:
    restoration of the original source after a true
    conull core, supporting 3.2.46, p. 282,
    by the reduction of 3.2.11, p. 249.
    Whole fibre masses agree almost everywhere, including
    infinite masses and nonmeasurable original fibres. *)
Corollary riemannian_coarea_null_source_fibre_agreement (R : realType) m n A B g h
    (hg : @is_continuous_riemannian_tensor R m A g)
    (hh : @is_continuous_riemannian_tensor R n B h)
    (f : riemannian_metric_space hg -> riemannian_metric_space hh)
    (hpSource : 0<=m%:R :> R) (hpTarget : 0<=n%:R :> R)
    (hpFibre : 0<=(m-n)%:R :> R) (C S : set (riemannian_metric_space hg)) :
  (n<=m)%N -> is_riemannian_path_lipschitz f -> C `<=` S ->
  riemannian_hausdorff_measure hg m%:R hpSource (S `\` C)=0%E ->
  measure_almost_everywhere (riemannian_hausdorff_measure hh n%:R hpTarget)
    [set y | riemannian_hausdorff_measure hg (m-n)%:R hpFibre (mapping_fibre f C y)=
      riemannian_hausdorff_measure hg (m-n)%:R hpFibre (mapping_fibre f S y)].
Proof.
move=> hnm hLip hCS hNull.
have hFibres := @riemannian_coarea_null_source_fibres R m n A B g h hg hh f
  hpSource hpTarget hpFibre hnm hLip (S `\` C) hNull.
apply:(@measure_almost_everywhere_mono R _ _
  (@riemannian_hausdorff_is_measure R n B h hh n%:R hpTarget) _ _ _ hFibres)=> y hy.
apply:(measure_null_modification_value
  (@riemannian_hausdorff_is_measure R m A g hg (m-n)%:R hpFibre) hy)=> x hx.
split.
- move=> [hc he]; split; last exact he; exact:hCS x hc.
- move=> [hs he]; split; last exact he.
  apply:contrapT=> hn; exact:(hx (conj (conj hs hn) he)).
Qed.
