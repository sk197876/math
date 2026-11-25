(** Federer (1969), 4.1.2, pp. 346–347: the
    nonnegative smooth kernel has compact support in the
    open unit ball and Lebesgue integral one. These
    independent laws precede existence and opaque selection. *)
From mathcomp Require Import all_boot all_order all_algebra reals classical_sets constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric GrassmannAbbreviations EuclideanInnerProduct InnerNorm HilbertFormCompactness
  NormRegularity CompactSupportFunctionUP EuclideanLebesgueDimensions MeasureIntegralUP SummableRealFunctionUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [is_smoothing_kernel]: the original conditions
    on Phi at the start of Federer 4.1.2,
    p. 346. Actual support and the actual
    Euclidean measure are retained, including dimension zero. *)
Record is_smoothing_kernel (R:realType) n (phi:R_n R n->R):Prop:={
  (** Source for [smoothing_kernel_smooth]: Phi is globally
      of class infinity, Federer 4.1.2, p. 346. *)
  smoothing_kernel_smooth:norm_class_all_orders
    (inner_norm_real_norm (@euclidean_inner_productP R n))
    (@scalar_absolute_value_norm R) (fun _=>True) phi;
  (** Source for [smoothing_kernel_nonnegative]: Phi is
      nonnegative, Federer 4.1.2, p. 346. *)
  smoothing_kernel_nonnegative:forall x,0<=phi x;
  (** Source for [smoothing_kernel_support_compact]: Phi has
      compact support, Federer 4.1.2, p. 346. *)
  smoothing_kernel_support_compact:@compact
    (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R n)))
    (@real_function_support R
      (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R n))) phi);
  (** Source for [smoothing_kernel_support_unit_ball]: the
      actual support lies in the open unit ball,
      Federer 4.1.2, p. 346. *)
  smoothing_kernel_support_unit_ball:
    @real_function_support R
      (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R n))) phi `<=`
      [set x|inner_norm (@euclidean_inner_productP R n) x<1];
  (** Source for [smoothing_kernel_integral_one]: the original
      Lebesgue integral of Phi equals one,
      Federer 4.1.2, p. 346. *)
  smoothing_kernel_integral_one:is_measure_integral (@euclidean_lebesgue_measure R n)
    (real_total_integrand phi) (1:R)%:E
}.
