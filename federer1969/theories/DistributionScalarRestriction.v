(** Federer (1969), 4.1.1, p. 345: T L u is the
    distribution phi to T(u phi). The actual test
    multiplier is continuous for the literal final topology,
    so its transpose is an actual weakly continuous linear
    operator on the distribution space. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals.
From Federer Require Import Hom RealNormUP NormDifferentialUP NormRegularity ContinuousMultilinearSealed
  OpenFamilyTopologyUP SmoothFunctionSpaceUP SmoothFunctionDerivativesUP SmoothTestSpaces SmoothTestTopology
  SmoothTestScalarMultiplier ContinuousRealDual ContinuousRealDualTranspose.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Section DistributionScalarRestriction.
Variable R:realType.
Variables X Y:lmodType R.
Variables (NX:X->R) (NY:Y->R).
Hypothesis hNX:is_real_norm NX.
Hypothesis hNY:is_real_norm NY.
Variable U:set X.
Hypothesis hU:forall x,U x ->norm_domain_interior NX U x.
Variable E:lmodType R.
Variable ev:E->X->Y.
Hypothesis hE:is_smooth_function_space hNX hNY U ev.
Local Notation Z := (fun k=>@ContinuousMultilinear.space R k X Y NX NY hNX hNY).
Variable D:forall k,X->Hom E (Z k).
Hypothesis hD:@is_smooth_function_derivatives R X Y NX NY hNX hNY U E ev D.
Variable u:X->R.
Hypothesis hu:norm_class_all_orders hNX (@scalar_absolute_value_norm R) U u.
Local Notation DT := (smooth_test_space hE).
Local Notation SO := (smooth_test_opens hE hD).
Local Notation hSO := (smooth_test_final_topology_laws hE hD).1.
Local Notation DD := (@continuous_real_dual_space R DT SO hSO).
Local Notation e := (@continuous_real_dual_evaluation R DT SO hSO).
Local Notation DO := (@continuous_real_dual_weak_opens R DT SO hSO).
Local Notation M := (@smooth_test_scalar_multiplier R X Y NX NY hNX hNY U E ev hE u hu).
Local Notation hM := (@smooth_test_scalar_multiplier_continuous R X Y NX NY hNX hNY U E ev hE
  u hu hU D hD).

(** Source for [distribution_scalar_restriction]: actual
    multiplication T L u, supporting the associated
    partition sum of Federer 4.1.1, p. 345. *)
Definition distribution_scalar_restriction:Hom DD DD:=
  @continuous_real_dual_transpose R DT DT SO SO hSO hSO M hM.

(** Source for [distribution_scalar_restriction_evaluation]:
    (T L u)(phi)=T(u phi), the exact definition
    in Federer 4.1.1, p. 345. *)
Theorem distribution_scalar_restriction_evaluation T f:
  e (distribution_scalar_restriction T) f=e T (M f).
Proof. exact:continuous_real_dual_transpose_evaluation. Qed.

(** Source for [distribution_scalar_restriction_continuous]:
    multiplication by a fixed smooth scalar is a weakly
    continuous linear endomorphism of D', supporting
    Federer 4.1.1, p. 345. *)
Theorem distribution_scalar_restriction_continuous:
  open_family_continuous DO DO distribution_scalar_restriction.
Proof. exact:continuous_real_dual_transpose_weak_continuous. Qed.
End DistributionScalarRestriction.
