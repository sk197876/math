(** Federer (1969), 4.1.5, p. 350:
    every original scalar test belongs to
    K(U), so a scalar Daniell integral
    can be restricted to the actual test
    space. No replacement test carrier is used. *)
From mathcomp Require Import all_boot all_order all_algebra functions classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormMetric SmoothFunctionSpaceUP SmoothTestSpaces SmoothTestEvaluation
  DistributionVariationDomain DistributionSubspaceTestValues CompactSupportFunctionUP CompactScalarVectorIdentification.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [smooth_scalar_test_original_compact_function]: the
    original inclusion D(U,R) into K(U)
    in the scalar Daniell assertion of
    Federer 4.1.5, p. 350. *)
Lemma smooth_scalar_test_original_compact_function (R:realType) (X:lmodType R)
    (NX:X->R) (hNX:is_real_norm NX) (U:set X) (E:lmodType R) (ev:E->X->R^o)
    (hE:is_smooth_function_space hNX (@scalar_absolute_value_norm R) U ev)
    (phi:smooth_test_space hE):
  @compactly_supported_continuous_functions R (set_type (U:set (real_norm_metric_space hNX)))
    (@distribution_domain_values R (real_norm_metric_space hNX) U R^o
      (smooth_test_space hE) (smooth_test_values_hom hE) phi).
Proof.
apply:compact_scalar_field_to_function.
exact:(@smooth_test_original_continuous_field R X R^o NX (fun t:R^o=>`|t|)
  hNX (@scalar_absolute_value_norm R) U E ev hE phi).
Qed.
