(** Federer (1969), 3.2.6, pp. 245–246: change
    of density for arbitrary real weights. Borel versions are
    selected only inside proofs; the actual density and original
    weight products retain their partial graphs. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology.
From Federer Require Import RealMetricBackground ExtendedRealOrderTopology ExtendedFiniteProjectionBorel
  RealLineSeparability PartialFunctionUP PartialFunctionBasic PartialFunctionPreimages PartialFunctionPostcomposition PartialDensityProduct
  MeasureUP MeasureAlmostUP MeasureAlmostBasic MeasureAlmostEquality MeasureIntegralUP MeasureIntegralAlmostEquality
  MeasureDensityUP MeasureDensityCover MeasureDensityTransfer PartialExtendedOrderLoci MeasureChangeOfDensity
  MeasurableFunctionUP MeasurablePostcomposition MeasurableGraphEquivalence MeasurableRealEmbedding
  MeasurableTotalBasic MeasurableAlmostModification BorelFunctionUP BorelRegularMeasureUP TopologicalBorel
  CountablyMeasurableUP LusinBorelVersion DensityNullWeightChange DensityRealWeightRecovery.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [density_measurable_real_weight_integral_iff]:
    supporting completed-measure step for Federer 3.2.6,
    pp. 245–246. Measurability for the density measure
    suffices; the original measure need not measure the real
    weight. Borel versions and the null-product law prove this. *)
Theorem density_measurable_real_weight_integral_iff (R:realType) (X:metricType R)
    (mu nu:set X->\bar R) (hm:is_measure mu)
    (hr:is_borel_regular_measure mu) (hs:is_borel_regular_measure nu)
    (h:partial_function X (extended_real_line R)) (g:X->real_line_metric R):
  is_measure_density mu h nu -> is_measure_measurable_function mu h ->
  measure_almost_everywhere mu (partial_extended_nonnegative_locus h) ->
  measure_countably_measurable nu setT ->
  is_measure_measurable_function nu (partial_function_total g) -> forall a,
  is_measure_integral nu (partial_function_total (fun x=>(g x)%:E:extended_real_line R)) a <->
  is_measure_integral mu
    (partial_density_product (partial_function_total (fun x=>(g x)%:E:extended_real_line R)) h) a.
Proof.
move=>hNu hh hp hCount hg a.
have hn:=@measure_density_is_measure R X mu nu hm h hNu hp.
have [D [hc hd]]:=real_line_countable_dense R.
have [G [hG hAgree]]:=@lusin_borel_version_metric R X [the metricType R of real_line_metric R]
  nu hn hs D (partial_function_total g) 0%R hc hd hg hCount.
have hGM:is_measure_measurable_function mu (partial_function_total G).
  constructor.
  - rewrite partial_function_total_domain; exact:measure_almost_everywhere_true hm.
  - move=>U hU; rewrite partial_function_total_preimage.
    exact (borel_regular_borel_measurable hm hr (hG U hU)).
have hGExtended:=measurable_total_real_embedding hm hGM.
have hRealAgree:measure_almost_everywhere nu [set x|G x=g x].
  apply:(@measure_almost_everywhere_mono R X nu hn _ _ _ hAgree)=>x [z [hz hGz]].
  change (g x=z) in hz; change (G x=z) in hGz; change (G x=g x); by rewrite hz hGz.
have hProducts:=density_null_real_weight_change hm hNu hh hp hRealAgree.
have hEmbed:measure_almost_equal nu
    (partial_function_total (fun x=>(G x)%:E:extended_real_line R))
    (partial_function_total (fun x=>(g x)%:E:extended_real_line R)).
  apply:(@measure_almost_everywhere_mono R X nu hn _ _ _ hRealAgree)=>x hx.
  exists (g x)%:E; split=>//; change ((G x)%:E=(g x)%:E); by rewrite hx.
have hIff:=@measure_density_integral_iff R X mu nu hm h
  (partial_function_total (fun x=>(G x)%:E:extended_real_line R)) hNu hh hp hGExtended a.
split=>hi.
- have hGInt:=measure_integral_almost_equal hn hi (measure_almost_equal_sym hEmbed).
  exact (measure_integral_almost_equal hm (hIff.1 hGInt) hProducts).
- have hGProd:=measure_integral_almost_equal hm hi (measure_almost_equal_sym hProducts).
  exact (measure_integral_almost_equal hn (hIff.2 hGProd) hEmbed).
Qed.

(** Source for [finite_density_arbitrary_real_weight_integral_iff]:
    supporting no-extra-measurability transformation for Federer
    3.2.6, p. 245. A finite nonnegative density recovers
    real-weight measurability from the product; thus the two
    integral graphs have exactly the same defined values. *)
Theorem finite_density_arbitrary_real_weight_integral_iff (R:realType) (X:metricType R)
    (mu nu:set X->\bar R) (hm:is_measure mu)
    (hr:is_borel_regular_measure mu) (hs:is_borel_regular_measure nu)
    (h:partial_function X (extended_real_line R)) (g:X->real_line_metric R):
  is_measure_density mu h nu -> is_measure_measurable_function mu h ->
  measure_almost_everywhere mu [set x|exists r:R,(0<=r)%R /\ partial_function_graph h x r%:E] ->
  measure_countably_measurable nu setT -> forall a,
  is_measure_integral nu (partial_function_total (fun x=>(g x)%:E:extended_real_line R)) a <->
  is_measure_integral mu
    (partial_density_product (partial_function_total (fun x=>(g x)%:E:extended_real_line R)) h) a.
Proof.
move=>hNu hh hFinite hCount a.
have hp:measure_almost_everywhere mu (partial_extended_nonnegative_locus h).
  apply:(@measure_almost_everywhere_mono R X mu hm _ _ _ hFinite)=>x [r [hr0 hRx]].
  exists r%:E; split=>//; by rewrite lee_fin.
have hn:=@measure_density_is_measure R X mu nu hm h hNu hp.
split=>hi.
- have hFine:=measurable_function_borel_postcomposition hn hi.1 (@extended_finite_projection_borel R).
  have hg:is_measure_measurable_function nu (partial_function_total g).
    apply:(@measurable_function_graph_equivalent R X [the topologicalType of real_line_metric R]
      nu _ (partial_function_total g) _ hFine)=>x z; split.
    + move=>[v [hv hz]]; change ((g x)%:E=v) in hv; by rewrite -hv /= in hz.
    + move=>hz; exists (g x)%:E; by split.
  exact ((density_measurable_real_weight_integral_iff hm hr hs hNu hh hp hCount hg a).1 hi).
- have hg:=finite_density_real_weight_recovery hm hNu hh hFinite hi.1.
  exact ((density_measurable_real_weight_integral_iff hm hr hs hNu hh hp hCount hg a).2 hi).
Qed.
