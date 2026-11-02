(** Federer (1969), 2.10.37, printed p. 198: apply 2.10.36 to every
    projected convex set, compare the actual projection norms, and divide by
    the positive beta_t(n,m). This proves the endpoint-product bound by m!
    zeta_t(S). The norm comparison is stated for Suslin convex sources,
    ensuring measurability of f_S; every open convex generator of Q_t has
    this property, so the final measure theorem will retain arbitrary
    targets. Infinite projected volumes and t=infinity are included. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct InnerMetric InnerConvex
  ScalarConvexLength ConvexEndpointVolumeBound EuclideanLinearMaps EuclideanLebesgueDimensions
  EuclideanProjectionSpace EuclideanProjectionMetric ExteriorDiameterUP ExteriorGrading FiniteExteriorPowers
  ExteriorMaps ExteriorOperatorEstimate ExteriorNorm SimpleElementary AssociatedSubspace
  OrthogonalProjectionConstants OrthogonalProjectionProbability ProjectionBeta ProjectionBetaContinuity
  SimpleProjectionExponentNorm ProjectedVolumeMeasurability IntegralGeometricGauge SuslinSetUP
  RealNormUP NormMetric ScalarNormExtendedEmbedding ExtendedRealOrderTopology
  PartialFunctionBasic MeasureUP MeasureAlmostUP MeasureAlmostBasic MeasurableFunctionUP
  MeasurableTotalBasic BorelFunctionBasic NonnegativeExtendedExponentNorm
  NonnegativeExtendedNormOrder NonnegativeExtendedNormScale.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [convex_projected_endpoint_volume_bound]: direct
    g(p)<=m! f_S(p) in the proof of
    2.10.37, p. 198, obtained from 2.10.36
    on the actual projected convex source.
    No measurability hypothesis is needed for this
    pointwise outer-volume comparison. *)
Theorem convex_projected_endpoint_volume_bound (R : realType) (n m : nat)
    (S : set (inner_metric_space (@euclidean_inner_productP R n)))
    (a b : 'I_m -> R_n R n) (p : orthogonal_projection_metric_space R n m) :
  (0<m)%N -> is_inner_convex S ->
  (forall i, S (a i)) -> (forall i, S (b i)) ->
  ((projection_norm (real_exterior_two_nonzero R) (exterior_difference_product a b) p)%:E <=
    (m`!)%:R%:E*projected_volume_function S p)%E.
Proof.
move=> hm hS ha hb.
pose q := euclidean_projection_linear p.
pose A : set (inner_metric_space (@euclidean_inner_productP R m)) := q @` S.
have hA : is_inner_convex A := linear_image_inner_convex hS.
have ha' i : A (q (a i)) by exists (a i); first exact: ha.
have hb' i : A (q (b i)) by exists (b i); first exact: hb.
have hh := @federer_2_10_36 R m A (fun i=>q (a i)) (fun i=>q (b i)) hm hA ha' hb'.
have he : exterior_power_map q m (exterior_difference_product a b)=
    e_lambda (fun i=>q (a i)-q (b i)) (ord_tuple m).
  have hf : (fun i : 'I_m=>q (a i-b i))=(fun i=>q (a i)-q (b i)).
    by apply: funext=> i; rewrite linearB.
  by rewrite /exterior_difference_product exterior_map_indexed_product hf.
change ((exterior_norm (real_exterior_two_nonzero R) (@euclidean_inner_productP R m)
    (exterior_power_map q m (exterior_difference_product a b)))%:E <=
    (m`!)%:R%:E*euclidean_lebesgue_measure m A)%E.
rewrite he (Prop_irrelevance (real_exterior_two_nonzero R) (euclidean_two_nonzero R)).
exact hh.
Qed.

(** Source for [convex_integral_geometric_endpoint_bound]: direct
    endpoint norm <= m! zeta_t(S), the
    last display in the proof of 2.10.37,
    p. 198. The supporting Suslin premise
    supplies the measurable projected-volume function;
    open convex generators satisfy it. The source
    can be unbounded and its gauge infinite. *)
Theorem convex_integral_geometric_endpoint_bound (R : realType) (n m : nat)
    (hmn : (m<=n)%N) (t : \bar R)
    (S : set (inner_metric_space (@euclidean_inner_productP R n)))
    (a b : 'I_m -> R_n R n) :
  (0<m)%N -> (1<=t)%E -> is_inner_convex S -> is_suslin_set R S ->
  (forall i, S (a i)) -> (forall i, S (b i)) ->
  ((exterior_difference_norm a b)%:E <=
    (m`!)%:R%:E*@integral_geometric_gauge R n m hmn t S)%E.
Proof.
move=> hm ht hS hs ha hb.
pose P := orthogonal_projection_metric_space R n m.
pose mu := @orthogonal_projection_probability R n m hmn.
have hmu : is_measure mu := @theta_star_is_measure R n m hmn.
pose xi := exterior_difference_product a b.
have hxi : simple xi := product_simple _.
pose g (p : P) : extended_real_line R := (projection_norm (real_exterior_two_nonzero R) xi p)%:E.
pose f (p : P) : extended_real_line R := projected_volume_function S p.
pose c : R := (m`!)%:R.
have hc : 0<=c by exact: ler0n.
have hcE : (0<=c%:E)%E by rewrite lee_fin.
have hg0 p : (0<=g p)%E by rewrite /g lee_fin; exact: projection_norm_nonnegative.
have hf0 p : (0<=f p)%E := projected_volume_function_nonnegative S p.
have hgs := @simple_projection_norm_scalar_measurable R n m hmn xi hxi.
have hg : is_measure_measurable_function mu (partial_function_total g).
  apply: (@measurable_total_borel_postcomposition R P
    [the topologicalType of real_norm_metric_space (scalar_absolute_value_norm R)]
    (extended_real_line R) mu hmu
    (fun p=>(projection_norm (real_exterior_two_nonzero R) xi p :
      real_norm_metric_space (scalar_absolute_value_norm R))) (fun y=>y%:E) hgs).
  apply: continuous_borel_function; exact: scalar_norm_extended_embedding_continuous.
have hf := @theta_star_projected_volume_measurable R n m hmn S hs.
have hscaled := @measurable_total_extended_scale R P mu hmu f c hf.
have hdom : measure_almost_everywhere mu [set p | (g p<=c%:E*f p)%E].
  apply: (@measure_almost_everywhere_mono R P mu hmu setT _ _
    (measure_almost_everywhere_true hmu))=> p _.
  exact: (@convex_projected_endpoint_volume_bound R n m S a b p hm hS ha hb).
have hn := @nonnegative_extended_norm_almost_order R P mu hmu g (fun p=>(c%:E*f p)%E) t
  hg0 (fun p=>mule_ge0 hcE (hf0 p)) ht hg hscaled hdom.
rewrite (@simple_projection_extended_exponent_norm R n m hmn xi t hxi ht)
  (@nonnegative_extended_norm_scale R P mu hmu f t c hf0 ht hc hf) in hn.
pose beta := @projection_beta R n m hmn t.
have hbeta : 0<beta := @projection_beta_positive R n m hmn t ht.
have hb0 : beta!=0 by rewrite gt_eqF.
have hbi : (0<=(beta^-1)%:E)%E by rewrite lee_fin invr_ge0; exact: ltW hbeta.
have hh := lee_wpmul2l hbi hn.
rewrite EFinM !muleA -EFinM mulVf // ?mul1e ?mul1r in hh.
rewrite [((beta^-1)%:E*c%:E)%E]muleC -muleA in hh.
exact hh.
Qed.
