(** Federer (1969), 3.2.33, p. 270: independent
    laws of the actual primitive g of the printed smooth series. *)
From mathcomp Require Import all_boot all_order all_algebra reals classical_sets constructive_ereal topology.
From Federer Require Import Hom RealNormUP NormRegularity NormDifferentialUP NormHigherCurveDerivativeUP
  RealMetricBackground RealOpenIntervals LipschitzUP PartialFunctionUP PartialFunctionBasic
  LebesgueScalarMeasure MeasureSubsetIntegral ExtendedRealOrderTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [is_interval_bump_primitive]: the integral definition,
    class infinity, increasing property and zero-derivative set
    of g in Federer 3.2.33, p. 270. All differentiability
    statements use the actual open unit interval; the total
    representative has no asserted off-domain regularity. The
    independent laws are proved from the series, not postulated. *)
Record is_interval_bump_primitive (R:realType) (a b:nat->R) (psi g:R->R):Prop:={
  (** Source for [interval_primitive_integral]: g(t) is the
      actual integral from zero to t of psi, Federer 3.2.33, p. 270. *)
  interval_primitive_integral:forall t,0<=t<= 1 ->
    is_measure_subset_integral (@lebesgue_scalar_measure R) `[0,t]
      (partial_function_total (fun s:real_line_metric R=>((psi s)%:E:extended_real_line R))) (g t)%:E;
  (** Source for [interval_primitive_differential]: g'=psi on
      T, supporting the printed critical-set equality in 3.2.33, p. 270. *)
  interval_primitive_differential:forall t,real_open_interval 0 1 t ->
    has_norm_differential (fun s:R^o=>`|s|) (fun s:R^o=>`|s|) (real_open_interval 0 1) g t
      (@scalar_coefficient_linear_map R R^o (psi t));
  (** Source for [interval_primitive_smooth]: g has class infinity
      on T, Federer 3.2.33, p. 270. *)
  interval_primitive_smooth:norm_class_all_orders (scalar_absolute_value_norm R)
    (scalar_absolute_value_norm R) (real_open_interval 0 1) g;
  (** Source for [interval_primitive_strict]: strict increase used
      for the fibre cubes in Federer 3.2.33, p. 270. *)
  interval_primitive_strict:forall u v,real_open_interval 0 1 u ->real_open_interval 0 1 v ->
    u<v ->g u<g v;
  (** Source for [interval_primitive_lipschitz]: supporting the
      hypotheses of 3.2.32 in the smooth example of 3.2.33, p. 270. *)
  interval_primitive_lipschitz:@is_metric_lipschitz_bound R (real_line_metric R)
    (real_line_metric R) (real_open_interval 0 1) g 1;
  (** Source for [interval_primitive_zero_coefficient]: the equality
      {g'= 0}=T minus V in Federer 3.2.33, p. 270, with
      the actual derivative coefficient supplied above. *)
  interval_primitive_zero_coefficient:forall t,real_open_interval 0 1 t ->
    (psi t= 0 <->~(\bigcup_j real_open_interval (a j) (b j)) t)
}.
