(** Federer (1969), 3.2.20, p. 256: the two displayed
    integrands for the original Lipschitz map f with domain W.
    The approximate Jacobian and the fibre count keep the actual
    partial graph, with no values supplied outside its domain. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric ExtendedRealOrderTopology
  PartialFunctionUP PartialFunctionBasic PartialFunctionPostcomposition PartialZeroExtension PartialDensityProduct
  MeasureRestriction HausdorffMeasure MeasureApproximateJacobian PartialMappingMultiplicity.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [rectifiable_area_source_integrand]: the left integrand
    g composed with f times ap J_m f in Federer 3.2.20,
    p. 256. The subset integral over W uses zero extension
    only outside W, following 2.4.10, p. 85; the intrinsic
    approximate Jacobian remains undefined off its actual domain. *)
Definition rectifiable_area_source_integrand (R : realType) m n k
    (W : set (R_n R n)) (f : partial_function (R_n R n) (R_n R k))
    (g : R_n R k -> \bar R) :=
  partial_function_zero_extension (0:extended_real_line R) W
    (partial_density_product (partial_function_postcompose f (fun y=>(g y:extended_real_line R)))
      (extended_measure_approximate_jacobian (measure_restrict
        (@hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R n)) m) W) m m f)).

(** Source for [rectifiable_area_target_integrand]: g(z) N(f,z)
    in Federer 3.2.20, p. 256. Count only actual values
    in the original partial map's graph. Infinite fibres and
    the distinguished zero-infinity product are retained. *)
Definition rectifiable_area_target_integrand (R : realType) n k
    (f : partial_function (R_n R n) (R_n R k)) (g : R_n R k -> \bar R) :=
  partial_function_total (fun z=>g z* @partial_mapping_multiplicity R _ _ f z : extended_real_line R).
