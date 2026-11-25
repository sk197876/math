(** Federer (1969), 3.2.13, p. 250: the angular
    function B(z), specified by its sphere integral on the
    positive-coordinate domain. Its existence is proved separately. *)
From mathcomp Require Import all_boot all_order all_algebra reals classical_sets constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerNorm InnerMetric
  GaussianProductIntegrand HausdorffMeasure PartialFunctionUP MeasureSubsetIntegral SummableRealFunctionUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [is_euler_beta]: the defining angular integral
    2B(z) in Federer 3.2.13, p. 250, with positive
    coordinate parameters. No Gamma product formula is assumed. *)
Record is_euler_beta (R:realType) m (B:partial_function (R_n R m) R):Prop:={
  (** Source for [euler_beta_graph_law]: the displayed sphere
      integral defining 2B(z), Federer 3.2.13, p. 250. *)
  euler_beta_graph_law:forall z a,partial_function_graph B z a <->
    (forall j,(0<z j)%R) /\is_measure_subset_integral
      (@hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R m)) (m-1))
      [set u|inner_norm (@euclidean_inner_productP R m) u= 1%R]
      (real_total_integrand (gaussian_angular_integrand z)) (2*a)%R%:E;
  (** Source for [euler_beta_domain_law]: B is finite on every
      positive-coordinate parameter family, Federer 3.2.13, p. 250. *)
  euler_beta_domain_law:forall z:R_n R m,(forall j,(0<z j)%R) ->exists a,partial_function_graph B z a;
  (** Source for [euler_beta_positive_law]: positivity of the
      angular normalization used in the Gamma quotient in Federer
      3.2.13, pp. 250–251; an implementation must prove it. *)
  euler_beta_positive_law:forall z a,partial_function_graph B z a ->(0<a)%R
}.
