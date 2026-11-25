(** Federer (1969), 3.2.5(2), p. 245, extended
    by 3.2.46, p. 282: recover the original real
    weight where the actual multiplicity is positive and
    finite. The actual infinite-multiplicity exceptional set
    is retained and proved null by the stated alternative. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp
  classical_sets constructive_ereal topology.
From Federer Require Import RealMetricBackground ExtendedRealOrderTopology ExtendedFiniteProjectionBorel RealReciprocalBorel
  RiemannianTensorUP RiemannianMetricCarrier RiemannianHausdorff RiemannianPathLipschitz
  RiemannianUnweightedArea RiemannianAreaTransformIntegrands
  PartialFunctionUP PartialFunctionBasic PartialFunctionPair PartialFunctionPostcomposition
  MeasureUP MeasureAlmostUP MeasurableFunctionUP MeasurableGraphEquivalence MeasurableTotalBasic MeasurableRealArithmetic
  MappingMultiplicity MappingMultiplicityLaws.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [riemannian_finite_multiplicity_weight_recovery]:
    the condition (2) recovery argument of 3.2.5,
    p. 245, with actual Riemannian measures in
    3.2.46, p. 282. Original integral-product
    measurability recovers a measurable weight representative
    on f(S) outside the actual null infinite-fibre set. *)
Theorem riemannian_finite_multiplicity_weight_recovery (R : realType) m n A B g h
    (hg : @is_continuous_riemannian_tensor R m A g)
    (hh : @is_continuous_riemannian_tensor R n B h)
    (f : riemannian_metric_space hg -> riemannian_metric_space hh)
    (hp : (0<=m%:R :> R)%R) (S : set (riemannian_metric_space hg))
    (u : riemannian_metric_space hh -> real_line_metric R) :
  is_riemannian_path_lipschitz f ->
  measure_measurable (riemannian_hausdorff_measure hg m%:R hp) S ->
  measure_almost_everywhere (riemannian_hausdorff_measure hh m%:R hp)
    [set y | @mapping_multiplicity R _ _ f S y< +oo] ->
  is_measure_measurable_function (riemannian_hausdorff_measure hh m%:R hp)
    (riemannian_area_target_integrand f S u) ->
  exists U N,
    is_measure_measurable_function (riemannian_hausdorff_measure hh m%:R hp) (partial_function_total U) /\
    riemannian_hausdorff_measure hh m%:R hp N=0 /\
    forall y, (f @` S) y -> ~ N y -> U y=u y.
Proof.
move=>hLip hS hFinite hTarget.
pose Y := [the metricType R of riemannian_metric_space hh].
pose beta := riemannian_hausdorff_measure hh m%:R hp.
have hb := @riemannian_hausdorff_is_measure R n B h hh m%:R hp.
pose M y:=@mapping_multiplicity R _ _ f S y.
have [a [hSource hCount]] := @riemannian_unweighted_area_formula R m n A B g h hg hh f hp S hLip hS.
pose F y:=(fine ((u y)%:E*M y):real_line_metric R).
pose V y:=(fine (M y):real_line_metric R).
pose U (y:Y):real_line_metric R:=(F y*(V y)^-1)%R.
have hF:=@measurable_total_borel_postcomposition R Y (extended_real_line R)
  [the topologicalType of real_line_metric R] beta hb
  (fun y=>((u y)%:E*M y:extended_real_line R)) (fun z=>(fine z:real_line_metric R))
  hTarget (@extended_finite_projection_borel R).
have hV:=@measurable_total_borel_postcomposition R Y (extended_real_line R)
  [the topologicalType of real_line_metric R] beta hb
  (fun y=>(M y:extended_real_line R)) (fun z=>(fine z:real_line_metric R))
  hCount.1 (@extended_finite_projection_borel R).
have hInv:=@measurable_total_borel_postcomposition R Y [the topologicalType of real_line_metric R]
  [the topologicalType of real_line_metric R] beta hb V (fun r=>(r^-1)%R) hV (@real_reciprocal_borel R).
have hProduct:=measurable_real_function_multiply hb hF hInv.
have hG:is_measure_measurable_function beta (partial_function_total U).
  apply:(@measurable_function_graph_equivalent R Y [the topologicalType of real_line_metric R]
    beta (partial_real_function_multiply (partial_function_total F)
      (partial_function_total (fun y=>((V y)^-1)%R))) (partial_function_total U) _ hProduct).
  move=>y z; split.
  - move=>[[r s] [[hr hs] he]]; change (F y=r) in hr; change (((V y)^-1)%R=s) in hs.
    change (U y=z); by rewrite /U hr hs.
  - move=>hz; change (U y=z) in hz; exists (F y,((V y)^-1)%R); by split; first split.
pose N:=(~` [set y|M y< +oo]).
exists U,N; split; first exact hG; split; first exact hFinite.
move=>y hImage hNot.
have hFin:M y< +oo by apply:contrapT=>hBad; exact (hNot hBad).
have hNonneg:0<=M y:=@mapping_multiplicity_nonnegative R _ _ f S y.
have hNum:M y \is a fin_num by rewrite (ge0_fin_numE hNonneg).
have hRep:M y=(fine (M y))%:E:=esym (fineK hNum).
have hNZ:M y<>0.
  move=>hZero; exact ((@mapping_multiplicity_zero_iff R _ _ f S y).1 hZero hImage).
have hV0:V y!=0%R.
  apply/negP=>/eqP hZero; apply:hNZ; by rewrite hRep -/(V y) hZero.
have hFValue:F y=(u y*V y)%R.
  by rewrite /F hRep -EFinM.
by rewrite /U hFValue -mulrA (mulfV hV0) mulr1.
Qed.
