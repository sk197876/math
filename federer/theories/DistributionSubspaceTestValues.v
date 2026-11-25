(** Federer (1969), 4.1.5, pp. 349–350:
    the original compact continuous extension on U
    agrees exactly with S on every original test.
    The public zero-extension and test-value laws
    prove the agreement. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormMetric SmoothFunctionSpaceUP SmoothTestSpaces SmoothTestEvaluation
  CompactContinuousVectorFields CompactContinuousSubspaceSupport CompactContinuousOpenExtensionInverse
  SmoothTestCompactContinuous DistributionVariationDomain DistributionContinuousExtensionUP DistributionSubspaceExtension.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section DistributionSubspaceTestValues.
Variable R:realType.
Variables X Y:lmodType R.
Variables (NX:X->R) (NY:Y->R).
Hypothesis hNX:is_real_norm NX.
Hypothesis hNY:is_real_norm NY.
Variable U:set X.
Variable E:lmodType R.
Variable ev:E->X->Y.
Hypothesis hE:is_smooth_function_space hNX hNY U ev.
Local Notation XT := (real_norm_metric_space hNX).
Local Notation UT := (set_type (U:set XT)).
Local Notation DT := (smooth_test_space hE).
Local Notation values := (smooth_test_values_hom hE).
Local Notation original := (@distribution_domain_values R XT U Y DT values).

(** Source for [smooth_test_original_continuous_field]:
    each original test restricted to U belongs to
    the compact continuous D of Federer 4.1.5,
    p. 349. *)
Theorem smooth_test_original_continuous_field phi:
  @compact_continuous_vector_fields R UT Y NY hNY (original phi).
Proof.
have hField:=@smooth_test_compact_continuous_field R X Y NX NY hNX hNY U E ev hE phi.
exact:(@compact_vector_open_restriction R XT U Y NY hNY _ hField.1 hField.2).
Qed.

(** Source for [distribution_subspace_test_value]:
    the original T on U extends S, as asserted
    in Federer 4.1.5, pp. 349–350. *)
Theorem distribution_subspace_test_value (S:Hom DT R^o) (T:(X->Y)->R):
  @is_distribution_continuous_extension R XT U Y NY hNY DT values S T ->
  forall phi:DT,@distribution_subspace_extension R XT U Y T (original phi)=S phi.
Proof.
move=>hT phi.
have hOff:forall x,~U x ->values phi x=0.
  move=>x hx; exact:(@smooth_test_value_outside R X Y NX NY hNX hNY U E ev hE phi x hx).
have hInverse:=@compact_vector_open_extension_restriction_inverse R XT U Y (values phi) hOff.
rewrite /distribution_subspace_extension.
change (T (@CompactContinuousVectorZeroExtension.compact_vector_open_extension R XT U Y
  (fun x:UT=>values phi (set_val x)))=S phi).
rewrite hInverse.
exact:(@distribution_extension_original R XT U Y NY hNY DT values S T hT phi).
Qed.
End DistributionSubspaceTestValues.
