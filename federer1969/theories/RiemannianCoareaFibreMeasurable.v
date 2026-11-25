(** Federer (1969), 3.2.46, p. 282: actual
    complementary fibre masses and fibre sets are measurable
    under exactly the original Lipschitz and source-volume
    measurability hypotheses. Compact cores and actual null
    fibres expand the reduction of 2.10.26, p. 190. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp
  classical_sets constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations RiemannianTensorUP RiemannianMetricCarrier
  RiemannianHausdorff RiemannianPathLipschitz RiemannianVolumeCompactCore
  RiemannianCoareaNullFibres RealHausdorffMeasure HausdorffMeasure HausdorffFibreCutoffs
  CompactUnionFibreMeasurability MappingMultiplicity LipschitzUP NormMetricScaleContinuity
  PartialFunctionUP PartialFunctionBasic MeasurableFunctionUP MeasurableAlmostModification
  MeasurableGraphEquivalence MeasureUP MeasureAlmostUP MeasureAlmostBasic
  TopologicalBorel ExtendedRealOrderTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [riemannian_hausdorff_natural_carrier]:
    the original rho measure in natural degree equals
    the natural-degree Hausdorff measure of its technical
    carrier, supporting 3.2.46, pp. 281–282.
    This follows from exact small-cutoff compatibility,
    not an assumed invariance under a nonlinear metric change. *)
Lemma riemannian_hausdorff_natural_carrier (R : realType) m A g
    (hg : @is_continuous_riemannian_tensor R m A g) k
    (hp : 0<=k%:R :> R) S :
  riemannian_hausdorff_measure hg k%:R hp S=
    @hausdorff_measure R (riemannian_metric_space hg) k S.
Proof. by rewrite riemannian_hausdorff_carrier real_hausdorff_measure_natural. Qed.

(** Source for [riemannian_coarea_fibre_mass_measurable]:
    measurability of the whole original complementary
    fibre mass in the extension of 3.2.11,
    p. 249, asserted in 3.2.46, p. 282.
    No finite-mass, Borel-source, rank or positive-target-
    dimension premise is supplied; infinite fibre masses
    and completed measurable source sets are retained. *)
Theorem riemannian_coarea_fibre_mass_measurable (R : realType) m n A B g h
    (hg : @is_continuous_riemannian_tensor R m A g)
    (hh : @is_continuous_riemannian_tensor R n B h)
    (f : riemannian_metric_space hg -> riemannian_metric_space hh)
    (hpSource : 0<=m%:R :> R) (hpTarget : 0<=n%:R :> R)
    (hpFibre : 0<=(m-n)%:R :> R) (S : set (riemannian_metric_space hg)) :
  (n<=m)%N -> is_riemannian_path_lipschitz f ->
  measure_measurable (riemannian_hausdorff_measure hg m%:R hpSource) S ->
  is_measure_measurable_function (riemannian_hausdorff_measure hh n%:R hpTarget)
    (partial_function_total (fun y=>(riemannian_hausdorff_measure hg (m-n)%:R hpFibre
      (mapping_fibre f S y) : extended_real_line R))).
Proof.
move=> hnm hLip hS.
pose X := [the metricType R of riemannian_metric_space hg].
pose Y := [the metricType R of riemannian_metric_space hh].
pose sigma := riemannian_hausdorff_measure hg (m-n)%:R hpFibre.
pose beta := riemannian_hausdorff_measure hh n%:R hpTarget.
have hBeta := @riemannian_hausdorff_is_measure R n B h hh n%:R hpTarget.
have [K [hKCompact [hKSubset [hIncreasing hNull]]]] :=
  @riemannian_volume_compact_core R m A g hg hpSource S hS.
pose C := \bigcup_j K j.
have hCS : C `<=` S by move=> x [j _ hx]; exact:hKSubset j x hx.
have hCont : continuous f.
  have [L [hL hBound]] := @riemannian_path_lipschitz_carrier R m n A B g h hg hh f hLip.
  apply:(@metric_fixed_lipschitz_continuous R X Y f L (ltW hL)).
  by move=> x y; exact:hBound.2 x y Logic.I Logic.I.
have hCoreMeas := @increasing_compact_fibre_mass_measurable R X Y f K (m-n) n
  hCont hKCompact hIncreasing.
have hTarget : beta=@hausdorff_measure R Y n.
  apply:funext=> T; exact:riemannian_hausdorff_natural_carrier.
have hCoreFunction : (fun y=>(sigma (mapping_fibre f C y) : extended_real_line R))=
    hausdorff_fibre_mass f C (m-n).
  apply:funext=> y; rewrite /sigma riemannian_hausdorff_natural_carrier.
  by [].
have hActualCore : is_measure_measurable_function beta
    (partial_function_total (fun y=>(sigma (mapping_fibre f C y) : extended_real_line R))).
  by rewrite hTarget hCoreFunction.
apply:(@measurable_function_almost_equal R Y (extended_real_line R) beta hBeta _ _ hActualCore).
have hAgreement := @riemannian_coarea_null_source_fibre_agreement R m n A B g h hg hh f
  hpSource hpTarget hpFibre C S hnm hLip hCS hNull.
apply:(@measure_almost_everywhere_mono R Y beta hBeta _ _ _ hAgreement)=> y hy.
exists (sigma (mapping_fibre f C y)); split; first by [].
exact:esym hy.
Qed.

(** Source for [riemannian_coarea_source_fibres_measurable]:
    almost every original fibre is genuinely measurable
    for complementary Riemannian Hausdorff measure, as
    required by the extension of 2.10.26, p. 189,
    in 3.2.46, p. 282. This is proved
    from compact cores and actual null fibre remainders,
    without assuming the original source Borel. *)
Theorem riemannian_coarea_source_fibres_measurable (R : realType) m n A B g h
    (hg : @is_continuous_riemannian_tensor R m A g)
    (hh : @is_continuous_riemannian_tensor R n B h)
    (f : riemannian_metric_space hg -> riemannian_metric_space hh)
    (hpSource : 0<=m%:R :> R) (hpTarget : 0<=n%:R :> R)
    (hpFibre : 0<=(m-n)%:R :> R) (S : set (riemannian_metric_space hg)) :
  (n<=m)%N -> is_riemannian_path_lipschitz f ->
  measure_measurable (riemannian_hausdorff_measure hg m%:R hpSource) S ->
  measure_almost_everywhere (riemannian_hausdorff_measure hh n%:R hpTarget)
    [set y | measure_measurable (riemannian_hausdorff_measure hg (m-n)%:R hpFibre)
      (mapping_fibre f S y)].
Proof.
move=> hnm hLip hS.
pose X := [the metricType R of riemannian_metric_space hg].
pose Y := [the metricType R of riemannian_metric_space hh].
pose sigma := riemannian_hausdorff_measure hg (m-n)%:R hpFibre.
pose beta := riemannian_hausdorff_measure hh n%:R hpTarget.
have hSigma := @riemannian_hausdorff_is_measure R m A g hg (m-n)%:R hpFibre.
have hBeta := @riemannian_hausdorff_is_measure R n B h hh n%:R hpTarget.
have [K [hKCompact [hKSubset [hIncreasing hNull]]]] :=
  @riemannian_volume_compact_core R m A g hg hpSource S hS.
pose C := \bigcup_j K j.
have hCS : C `<=` S by move=> x [j _ hx]; exact:hKSubset j x hx.
have hCont : continuous f.
  have [L [hL hBound]] := @riemannian_path_lipschitz_carrier R m n A B g h hg hh f hLip.
  apply:(@metric_fixed_lipschitz_continuous R X Y f L (ltW hL)).
  by move=> x y; exact:hBound.2 x y Logic.I Logic.I.
have hCoreMeas y : measure_measurable sigma (mapping_fibre f C y).
  have hSigmaValue : sigma=@hausdorff_measure R X (m-n).
    apply:funext=> T; exact:riemannian_hausdorff_natural_carrier.
  rewrite hSigmaValue.
  exact (@countable_compact_union_fibres_measurable R X Y f K (m-n) hCont hKCompact y).
have hFibres := @riemannian_coarea_null_source_fibres R m n A B g h hg hh f
  hpSource hpTarget hpFibre hnm hLip (S `\` C) hNull.
apply:(@measure_almost_everywhere_mono R Y beta hBeta _ _ _ hFibres)=> y hy.
apply:(@measurable_set_null_modification R X sigma hSigma
  (mapping_fibre f C y) (mapping_fibre f S y) (mapping_fibre f (S `\` C) y)
  hy _ (hCoreMeas y))=> x hx.
split.
- move=> [hc he]; split; last exact he; exact:hCS x hc.
- move=> [hs he]; split; last exact he.
  apply:contrapT=> hn; exact:(hx (conj (conj hs hn) he)).
Qed.
