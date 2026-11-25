(** Federer (1969), 3.2.46, p. 282: the actual
    Riemannian area integrand is measurable on its original
    differential domain. Use the already proved Borel graph
    of Df and the genuine Gram-Jacobian continuity, without
    extending Df by a chosen field or assigning default values. *)
From mathcomp Require Import all_boot all_order all_algebra reals
  classical_sets constructive_ereal topology.
From Federer Require Import Hom TensorUP GrassmannAbbreviations FiniteCoordinates
  EuclideanInnerProduct InnerNorm InnerMetric HilbertFormCompactness NormMetric
  NormDifferentialUP NormMetricScaleContinuity NormClassZeroWhole NormClassOneUP
  ContinuousOperatorUP ContinuousOperatorNorm EuclideanHomOperator HomSpaceNormTopology
  MetricProductBackground TopologicalProductMaps RealMetricBackground
  TopologicalBorel ContinuousBorelPreimages NormDifferentialBorelTests
  RiemannianTensorUP RiemannianLinearJacobian RiemannianTargetJacobian
  RiemannianAreaJacobianContinuity PartialFunctionUP
  EuclideanLebesgueDimensions MeasureUP MeasureAlmostUP MeasureAlmostBasic
  BorelRegularMeasureUP MeasurableFunctionUP MeasureStepIntegralIdentification
  InnerOwnNormTopology LipschitzUP Rademacher.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [target_riemannian_area_jacobian_borel_preimage]:
    every Borel preimage of the actual area Jacobian is
    Borel on the ordinary source, supporting 3.2.46,
    p. 282. The genuine differential graph test retains
    all singular maps and the exact partial domain. *)
Theorem target_riemannian_area_jacobian_borel_preimage (R : realType) m n A h
    (hh : @is_continuous_riemannian_tensor R n A h)
    (f : inner_metric_space (@euclidean_inner_productP R m) ->
      inner_metric_space (@euclidean_inner_productP R n))
    (hf : forall x, A (f x)) :
  is_metric_lipschitz setT f -> forall V : set (real_line_metric R), borel_set V ->
  @borel_set [the topologicalType of inner_metric_space (@euclidean_inner_productP R m)]
    (partial_function_preimage (@target_riemannian_jacobian R m n A h hh f hf m) V).
Proof.
move=> hLip V hV.
pose NX := inner_norm (@euclidean_inner_productP R m).
pose NY := inner_norm (@euclidean_inner_productP R n).
pose hNX := inner_norm_real_norm (@euclidean_inner_productP R m).
pose hNY := inner_norm_real_norm (@euclidean_inner_productP R n).
pose ev := hom_of_linear (linear_id (Hom (R_n R m) (R_n R n))).
pose hZ := @euclidean_hom_operator_space R m n.
pose E := [the metricType R of real_norm_metric_space hNX].
pose T := [the metricType R of real_norm_metric_space (continuous_operator_norm_is_norm hNY hZ)].
pose P := [the metricType R of metric_product E T].
have hCont : continuous (fun x : E=>(f x : inner_metric_space (@euclidean_inner_productP R n))).
  have [K [hK hBound]] := hLip.
  apply: (@metric_fixed_lipschitz_continuous R E
    [the metricType R of inner_metric_space (@euclidean_inner_productP R n)] f K (ltW hK)).
  by move=> x y; exact: hBound.2 x y Logic.I Logic.I.
have hContNorm : continuous (fun x : E=>(f x : real_norm_metric_space hNY)).
  have [K [hK hBound]] := hLip.
  apply: (@metric_fixed_lipschitz_continuous R E
    [the metricType R of real_norm_metric_space hNY] f K (ltW hK)).
  by move=> x y; exact: hBound.2 x y Logic.I Logic.I.
have hZero := @norm_continuous_whole_class_zero R (R_n R m) (R_n R n)
  NX NY hNX hNY f hContNorm.
pose Q := fun p : P=>riemannian_linear_jacobian (@euclidean_inner_productP R m)
  (riemannian_tensor_inner hh (hf p.1)) m p.2.
have hParameter : continuous (fun p : P=>(f p.1 : inner_metric_space (@euclidean_inner_productP R n))).
  move=> p; exact (continuous_comp (@first_projection_continuous E T p) (hCont p.1)).
have hQ : continuous (fun p : P=>(Q p : real_line_metric R)).
  exact (@riemannian_area_jacobian_continuous_parameter R m n A h hh P
    (fun p=>f p.1) (fun p=>hf p.1) (fun p=>p.2) hParameter
    (@second_projection_continuous E T)).
pose C : set P := Q @^-1` V.
have hC : @borel_set P C := @continuous_borel_preimage P (real_line_metric R) Q hQ V hV.
have [q [b hb]] := @hom_space_finite_basis R (R_n R m) (R_n R n)
  m (@coordinate_basis R m) (@coordinate_basisP R m)
  n (@coordinate_basis R n) (@coordinate_basisP R n).
have hTest := @norm_differential_borel_domain_test R (R_n R m) (R_n R n)
  (Hom (R_n R m) (R_n R n)) NX NY hNX hNY ev (@euclidean_operator_norm R m n)
  hZ m (@coordinate_basis R m) (@coordinate_basisP R m) q b hb setT f hZero C hC.
have hEqual : [set a : E | exists D, has_norm_differential NX NY setT f a (ev D) /\ C (a,D)] =
    partial_function_preimage (@target_riemannian_jacobian R m n A h hh f hf m) V.
  apply/seteqP; split=> a.
  - move=> [D [hD hVal]].
    exists (riemannian_linear_jacobian (@euclidean_inner_productP R m)
      (riemannian_tensor_inner hh (hf a)) m D); split; last exact hVal.
    apply: (@target_riemannian_jacobian_graph R m n A h hh f hf m a _).2.
    exists D; by split.
  - move=> [j [hJ hVal]].
    have [D [hD hValue]] := (@target_riemannian_jacobian_graph R m n A h hh f hf m a j).1 hJ.
    exists D; split; first exact hD.
    change (V (riemannian_linear_jacobian (@euclidean_inner_productP R m)
      (riemannian_tensor_inner hh (hf a)) m D)); by rewrite hValue.
rewrite hEqual in hTest.
exact: (inner_own_norm_borel_iff (@euclidean_inner_productP R m) _).2 hTest.
Qed.

(** Source for [target_riemannian_area_jacobian_measurable]:
    the Riemannian area Jacobian is Lebesgue measurable,
    supporting 3.2.46, p. 282. Rademacher supplies
    the conull exact differential domain; the Borel graph
    argument supplies open preimages. *)
Theorem target_riemannian_area_jacobian_measurable (R : realType) m n A h
    (hh : @is_continuous_riemannian_tensor R n A h)
    (f : inner_metric_space (@euclidean_inner_productP R m) ->
      inner_metric_space (@euclidean_inner_productP R n)) (hf : forall x, A (f x)) :
  is_metric_lipschitz setT f ->
  @is_measure_measurable_function R
    [the choiceType of inner_metric_space (@euclidean_inner_productP R m)]
    [the topologicalType of real_line_metric R] (@euclidean_lebesgue_measure R m)
    (@target_riemannian_jacobian R m n A h hh f hf m).
Proof.
move=> hLip; constructor.
- apply: (@measure_almost_everywhere_mono R _ _ (euclidean_lebesgue_is_measure R m)
    _ _ _ (federer_3_1_6 hLip))=> a [D hD].
  exists (riemannian_linear_jacobian (@euclidean_inner_productP R m)
    (riemannian_tensor_inner hh (hf a)) m D).
  apply: (@target_riemannian_jacobian_graph R m n A h hh f hf m a _).2.
  exists D; by split.
- move=> V hV.
  exact (@borel_regular_borel_measurable R
    [the topologicalType of inner_metric_space (@euclidean_inner_productP R m)]
    (@euclidean_lebesgue_measure R m) (euclidean_lebesgue_is_measure R m)
    (euclidean_lebesgue_borel_regular R m) _
    (@target_riemannian_area_jacobian_borel_preimage R m n A h hh f hf hLip V (open_borel_set hV))).
Qed.

(** Source for [extended_target_riemannian_area_jacobian_measurable]:
    the same actual partial integrand is measurable for the
    extended-real integral, supporting 3.2.46, p. 282.
    Embedding changes neither its domain nor its real values. *)
Theorem extended_target_riemannian_area_jacobian_measurable (R : realType) m n A h
    (hh : @is_continuous_riemannian_tensor R n A h)
    (f : inner_metric_space (@euclidean_inner_productP R m) ->
      inner_metric_space (@euclidean_inner_productP R n)) (hf : forall x, A (f x)) :
  is_metric_lipschitz setT f ->
  is_measure_measurable_function (@euclidean_lebesgue_measure R m)
    (@extended_target_riemannian_jacobian R m n A h hh f hf m).
Proof.
move=> hLip.
exact (@measurable_partial_real_embedding R _ (@euclidean_lebesgue_measure R m)
  (euclidean_lebesgue_is_measure R m) _
  (@target_riemannian_area_jacobian_measurable R m n A h hh f hf hLip)).
Qed.
