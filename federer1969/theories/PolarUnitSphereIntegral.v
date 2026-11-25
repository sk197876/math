(** Federer (1969), 3.2.13, p. 250: the
    unit-sphere inner integral and its radial
    factor are specified by the existing opaque
    parameterized integral, retaining exact signed domains. *)
From mathcomp Require Import all_boot all_order all_algebra reals classical_sets constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerNorm InnerMetric
  SphereDilationMeasure SphereDilationIntegral EuclideanSphereMeasurable RadialSphereIntegral
  HausdorffMeasure MeasureUP MeasureRestriction RestrictedIntegralIdentity
  PartialFunctionUP PartialFunctionBasic PartialFunctionPrecomposition PartialZeroExtension
  ParameterizedIntegral ParameterizedIntegralLaws PartialDensityProduct MeasureIntegralUP
  MeasureSubsetIntegral ExtendedRealOrderTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [unit_sphere_dilation_integral]: the inner
    integral of g(r u) on |u|= 1
    in the second polar formula of Federer
    3.2.13, p. 250. No value is
    assigned when that actual signed integral is undefined. *)
Definition unit_sphere_dilation_integral (R:realType) m
    (u:partial_function (R_n R m) (extended_real_line R)):=
  parameterized_integral (@hausdorff_measure R
    (inner_metric_space (@euclidean_inner_productP R m)) (m-1))
    (fun r:R=>partial_function_zero_extension (0:extended_real_line R)
      [set x|inner_norm (@euclidean_inner_productP R m) x= 1%R]
      (partial_function_precompose (fun x:R_n R m=>r*:x) u)).

(** Source for [unit_sphere_dilation_integral_graph]: the
    exact inner-integral graph in the second
    identity of Federer 3.2.13, p. 250. *)
Lemma unit_sphere_dilation_integral_graph (R:realType) m u (r:R) b:
  partial_function_graph (@unit_sphere_dilation_integral R m u) r b <->
  is_measure_subset_integral (@hausdorff_measure R
    (inner_metric_space (@euclidean_inner_productP R m)) (m-1))
    [set x|inner_norm (@euclidean_inner_productP R m) x= 1%R]
    (partial_function_precompose (fun x:R_n R m=>r*:x) u) b.
Proof. exact:parameterized_integral_specification. Qed.

(** Source for [weighted_unit_sphere_integral]: the
    r^(m-1) times unit-sphere inner integral
    in Federer 3.2.13, p. 250.
    Only positive radii enter the final outer integral. *)
Definition weighted_unit_sphere_integral (R:realType) m
    (u:partial_function (R_n R m) (extended_real_line R)):=
  partial_density_product (unit_sphere_dilation_integral u)
    (partial_function_total (fun r:R=>((r^+(m-1))%R%:E:extended_real_line R))).

(** Source for [radial_unit_sphere_integral_graph]: the
    exact change of inner sphere integrals in
    the second polar formula, Federer 3.2.13,
    p. 250. Both directions preserve definedness,
    including finite and signed infinite values. *)
Lemma radial_unit_sphere_integral_graph (R:realType) m u (r:R) a:
  (0<r)%R ->
  (partial_function_graph (@radial_sphere_integral R m u) r a <->
    partial_function_graph (weighted_unit_sphere_integral u) r a).
Proof.
move=>hr.
pose X:=inner_metric_space (@euclidean_inner_productP R m).
pose H:=@hausdorff_measure R X (m-1).
pose hH:=@hausdorff_measure_is_measure R X (m-1).
pose d:=fun x:R_n R m=>r*:x.
pose c:=(r^+(m-1))%R.
have hc:(0<c)%R:=exprn_gt0 (m-1)%N hr.
have hcNe:(c!= 0)%R:=lt0r_neq0 hc.
have hSr:=@euclidean_norm_sphere_hausdorff_measurable R m (m-1) r.
have hS1:=@euclidean_norm_sphere_hausdorff_measurable R m (m-1) 1%R.
have hRadius:=@restricted_integral_zero_extension_iff R X H hH
  [set x|inner_norm (@euclidean_inner_productP R m) x=r] u a hSr.
split.
- move/radial_sphere_integral_graph=>hI.
  have hRestricted:=hRadius.2 hI.
  have hUnitRestricted:=(@sphere_dilation_integral_iff R m (m-1) r u a hr).1 hRestricted.
  have hUnitSubset:=(@restricted_integral_zero_extension_iff R X H hH
    [set x|inner_norm (@euclidean_inner_productP R m) x= 1%R] (partial_function_precompose d u)
    ((c^-1)%R%:E*a) hS1).1 hUnitRestricted.
  have hInner:partial_function_graph (unit_sphere_dilation_integral u) r ((c^-1)%R%:E*a).
    apply/unit_sphere_dilation_integral_graph; exact hUnitSubset.
  apply/partial_density_product_graph; exists ((c^-1)%R%:E*a),c%:E; split=>//; split; first by [].
  by rewrite muleC muleA -EFinM mulfV // mul1e.
- move/partial_density_product_graph=>[b [z [hInner [hz hValue]]]].
  change (c%:E=z) in hz; rewrite -hz in hValue.
  have hUnitSubset:=(@unit_sphere_dilation_integral_graph R m u r b).1 hInner.
  have hUnitRestricted:=(@restricted_integral_zero_extension_iff R X H hH
    [set x|inner_norm (@euclidean_inner_productP R m) x= 1%R] (partial_function_precompose d u) b hS1).2 hUnitSubset.
  have hScaled:b=(c^-1)%R%:E*a.
    rewrite -hValue [b*c%:E]muleC muleA -EFinM mulVf // mul1e; by [].
  rewrite hScaled in hUnitRestricted.
  have hRestricted:=(@sphere_dilation_integral_iff R m (m-1) r u a hr).2 hUnitRestricted.
  apply/radial_sphere_integral_graph; exact:hRadius.1 hRestricted.
Qed.
