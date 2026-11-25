(** Federer (1969), 3.2.22(3), p. 258:
    the original-domain source integrand and the actual
    fibre integral, with the intrinsic mu-Jacobian. *)
From mathcomp Require Import all_boot all_order all_algebra reals classical_sets constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric ExtendedRealOrderTopology
  PartialFunctionUP PartialZeroExtension PartialDensityProduct PartialMappingMultiplicity
  MeasureRestriction HausdorffMeasure MeasureApproximateJacobian ParameterizedIntegral.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [rectifiable_coarea_source_integrand]: the
    left integrand g times ap J_mu f in Federer
    3.2.22(3), p. 258. Density dimension m and
    exterior degree mu stay separate. The zero extension
    is only outside W; both the original weight and
    the approximate Jacobian keep their actual domains
    on W. The supporting definition admits extended weights;
    the numbered real-weight theorem is proved separately. *)
Definition rectifiable_coarea_source_integrand (R:realType) m n mu v
    (W:set (R_n R n)) (f:partial_function (R_n R n) (R_n R v))
    (g:partial_function (R_n R n) (extended_real_line R)):=
  partial_function_zero_extension (0:extended_real_line R) W
    (partial_density_product g
      (extended_measure_approximate_jacobian (measure_restrict
        (@hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R n)) m) W) m mu f)).

(** Source for [rectifiable_coarea_fibre_integral]: the
    inner integral over the actual f inverse {z}
    in Federer 3.2.22(3), p. 258. Only
    points in the original partial graph contribute.
    The existing opaque parameterized-integral laws give
    exactly the parameters where the signed fibre
    integral exists; no default is assigned elsewhere. *)
Definition rectifiable_coarea_fibre_integral (R:realType) m n mu v
    (f:partial_function (R_n R n) (R_n R v))
    (g:partial_function (R_n R n) (extended_real_line R)):=
  parameterized_integral (@hausdorff_measure R
    (inner_metric_space (@euclidean_inner_productP R n)) (m-mu))
    (fun z=>partial_function_zero_extension (0:extended_real_line R) (partial_mapping_fibre f z) g).
