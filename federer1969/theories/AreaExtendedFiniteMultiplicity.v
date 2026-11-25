(** Federer (1969), 3.2.20, p. 257: supporting
    extended-real form of the two applications of 3.2.5(2),
    pp. 244–245. The finite-multiplicity premise is later discharged
    separately on every compact parameter chart. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric EuclideanLebesgueDimensions
  RealMetricBackground ExtendedRealOrderTopology ExtendedFiniteProjectionBorel
  PartialFunctionUP PartialFunctionBasic PartialZeroExtension PartialDensityProduct
  MeasureUP MeasureAlmostUP MeasureAlmostBasic MeasureAlmostEquality MeasurableFunctionUP
  MeasurableTotalBasic MeasurableRealEmbedding MeasurableZeroExtension
  MeasureIntegralUP MeasureIntegralAlmostEquality LipschitzUP HausdorffMeasure MappingMultiplicity
  MappingMultiplicityLaws Jacobian EuclideanJacobianMeasurable EuclideanAreaFormula
  AreaTransformIntegrands AreaIntegralTransformation AreaExtendedTransformIntegrands
  FiniteDensityRepresentative ZeroExtendedDensityWeightAgreement
  FiniteWeightIntegralTransportUP FiniteWeightExtendedTransport.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [area_extended_finite_multiplicity_transform]: supporting
    extension of Federer 3.2.5(2), pp. 244–245, to the
    extended-real weight required by 3.2.20, p. 257. The
    original partial ordinary Jacobian domain is retained. Both signed
    infinite values and undefined differences are matched exactly;
    neither g-measurability nor integral existence is assumed. *)
Theorem area_extended_finite_multiplicity_transform (R : realType) m n
    (f : inner_metric_space (@euclidean_inner_productP R m) ->
      inner_metric_space (@euclidean_inner_productP R n)) (A : set (R_n R m)) :
  is_metric_lipschitz setT f ->
  measure_measurable (@euclidean_lebesgue_measure R m) A ->
  measure_almost_everywhere (@hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R n)) m)
    [set y|@mapping_multiplicity R _ _ f A y< +oo] ->
  forall (g : R_n R n -> \bar R) a,
    is_measure_integral (@euclidean_lebesgue_measure R m) (area_extended_source_integrand f A g) a <->
    is_measure_integral (@hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R n)) m)
      (area_extended_target_integrand f A g) a.
Proof.
move=> hLip hA hFinite.
pose X := inner_metric_space (@euclidean_inner_productP R m).
pose Y := inner_metric_space (@euclidean_inner_productP R n).
pose mu := @euclidean_lebesgue_measure R m.
pose nu := @hausdorff_measure R Y m.
have hm := euclidean_lebesgue_is_measure R m.
have hn := @hausdorff_measure_is_measure R Y m.
pose d := partial_function_zero_extension (0%R:real_line_metric R) A (euclidean_jacobian m setT f).
have hd : is_measure_measurable_function mu d :=
  @measurable_zero_extension R X [the topologicalType of real_line_metric R] mu hm (0%R:real_line_metric R) A
    (euclidean_jacobian m setT f) hA (euclidean_top_jacobian_measurable hLip).
have hdPos x j : partial_function_graph d x j -> (0<=j)%R.
  move=> hj; case: (pselect (A x))=> hx.
  - have hJ := (partial_function_zero_extension_on _ _ _ hx).1 hj.
    exact: (euclidean_jacobian_nonnegative hJ).
  - have hj0 : j=0%R := (partial_function_zero_extension_off _ _ _ hx).1 hj.
    by rewrite hj0.
have [p [hp [hpMeas [hpExt hpAE]]]] := nonnegative_finite_density_representative hm hd hdPos.
pose M y := @mapping_multiplicity R X Y f A y.
pose q (y : Y) : real_line_metric R := fine (M y).
have hq y : (0<=q y)%R.
  have hh := @mapping_multiplicity_nonnegative R X Y f A y.
  rewrite /q /M; by case: (@mapping_multiplicity R X Y f A y) hh=> [r| |] //=; rewrite lee_fin.
have [b [hArea hCount]] := euclidean_area_formula hLip hA.
have hqRealMeas : is_measure_measurable_function nu (partial_function_total q).
  exact: (@measurable_total_borel_postcomposition R Y (extended_real_line R)
    [the topologicalType of real_line_metric R] nu hn
    (fun y=>(M y:extended_real_line R)) (fun z=>(fine z:real_line_metric R))
    hCount.1 (@extended_finite_projection_borel R)).
have hqMeas := measurable_total_real_embedding hn hqRealMeas.
have hSource (g : Y -> \bar R) : measure_almost_equal mu
    (area_extended_source_integrand f A g)
    (partial_function_total (fun x=>g (f x)* (p x)%:E : extended_real_line R)).
  exact: (@zero_extended_density_weight_agreement R X mu hm A
    (euclidean_jacobian m setT f) p (fun x=>(g (f x):extended_real_line R))
    (measurable_function_domain hd) hpExt).
have hTarget (g : Y -> \bar R) : measure_almost_equal nu
    (area_extended_target_integrand f A g)
    (partial_function_total (fun y=>g y* (q y)%:E : extended_real_line R)).
  apply: (@measure_almost_everywhere_mono R Y nu hn _ _ _ hFinite)=> y hy.
  have hM0 : 0<=M y := @mapping_multiplicity_nonnegative R X Y f A y.
  have hMFin : M y \is a fin_num by rewrite (ge0_fin_numE hM0).
  have hEq : (q y)%:E=M y := fineK hMFin.
  exists (g y* M y); split; first reflexivity.
  by change (g y* (q y)%:E=g y* M y); rewrite hEq.
have hTransport : is_finite_weight_pair_transport mu nu f (fun y:Y=>y) p q.
  move=> h a.
  have hS := hSource (fun y=>(h y)%:E).
  have hT := hTarget (fun y=>(h y)%:E).
  have hFormula := @euclidean_area_integral_transformation R m n f A h hLip hA
    (or_intror (or_introl hFinite)) a.
  split=> hI.
  - have hOldS := measure_integral_almost_equal hm hI (measure_almost_equal_sym hS).
    have hOldT := hFormula.1 hOldS.
    exact: (measure_integral_almost_equal hn hOldT hT).
  - have hOldT := measure_integral_almost_equal hn hI (measure_almost_equal_sym hT).
    have hOldS := hFormula.2 hOldT.
    exact: (measure_integral_almost_equal hm hOldS hS).
have hExtended := @finite_weight_extended_integral_transport R X Y Y mu nu hm hn f
  (fun y:Y=>y) p q hp hq hpMeas hqMeas hTransport.
move=> g a; split=> hI.
- have hIS := measure_integral_almost_equal hm hI (hSource g).
  have hIT := (hExtended g a).1 hIS.
  exact: (measure_integral_almost_equal hn hIT (measure_almost_equal_sym (hTarget g))).
- have hIT := measure_integral_almost_equal hn hI (hTarget g).
  have hIS := (hExtended g a).2 hIT.
  exact: (measure_integral_almost_equal hm hIS (measure_almost_equal_sym (hSource g))).
Qed.
