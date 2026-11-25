(** Federer (1969), 4.1.1, p. 346: actual distributional
    directional derivatives, defined by the negative transpose
    of actual test-function differentiation. Standard basis
    directions give the printed D_j operators. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals.
From Federer Require Import Hom RealNormUP NormDifferentialUP ContinuousMultilinearSealed
  OpenFamilyTopologyUP SmoothFunctionSpaceUP SmoothFunctionDerivativesUP
  SmoothDirectionalDerivativeSealed SmoothTestSpaces SmoothTestTopology TestDirectionalOperator
  ContinuousRealDual ContinuousRealDualScaledTranspose.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

Section DistributionDifferentiation.
Variable R:realType.
Variables X Y:lmodType R.
Variables (NX:X->R) (NY:Y->R).
Hypothesis hNX:is_real_norm NX.
Hypothesis hNY:is_real_norm NY.
Variable U:set X.
Hypothesis hU:forall x,U x -> norm_domain_interior NX U x.
Variable E:lmodType R.
Variable ev:E->X->Y.
Hypothesis hE:is_smooth_function_space hNX hNY U ev.
Local Notation Z := (fun k=>@ContinuousMultilinear.space R k X Y NX NY hNX hNY).
Variable D:forall k,X->Hom E (Z k).
Hypothesis hD:@is_smooth_function_derivatives R X Y NX NY hNX hNY U E ev D.
Variable v:X.
Local Notation P := (@SmoothDirectionalDerivative.operator R X Y NX NY hNX hNY U E ev hE D hD v).
Local Notation hP := (@SmoothDirectionalDerivative.laws R X Y NX NY hNX hNY U E ev hE D hD v).
Local Notation DT := (smooth_test_space hE).
Local Notation SO := (smooth_test_opens hE hD).
Local Notation hSO := (smooth_test_final_topology_laws hE hD).1.
Local Notation DD := (@continuous_real_dual_space R DT SO hSO).
Local Notation e := (@continuous_real_dual_evaluation R DT SO hSO).
Local Notation DO := (@continuous_real_dual_weak_opens R DT SO hSO).
Local Notation TOp := (@test_directional_operator R X Y NX NY hNX hNY U hU E ev hE D hD v P hP).
Local Notation hTOp := (@test_directional_operator_continuous R X Y NX NY hNX hNY U hU E ev hE D hD v P hP).

(** Source for [distribution_test_directional_derivative]: the
    actual test-function derivative used in TD_j, supporting
    Federer 4.1.1, p. 346. Both its existence and continuity
    have already been proved for the original final topology. *)
Definition distribution_test_directional_derivative:Hom DT DT:=TOp.

(** Source for [distribution_directional_derivative]: D_v T is
    the negative transpose of test differentiation, the direct
    directional form of D_j T=-TD_j in Federer 4.1.1, p. 346. *)
Definition distribution_directional_derivative:Hom DD DD:=
  @continuous_real_dual_scaled_transpose R DT DT SO SO hSO hSO TOp hTOp (-1).

(** Source for [distribution_directional_derivative_evaluation]:
    (D_v T)(phi)=-T(D_v phi), the sign convention of Federer
    4.1.1, p. 346. All function and dual operators here are
    actual proved objects, not hypothetical action interfaces. *)
Theorem distribution_directional_derivative_evaluation T f:
  e (distribution_directional_derivative T) f=
    -e T (distribution_test_directional_derivative f).
Proof.
have h:=@continuous_real_dual_scaled_transpose_evaluation R DT DT SO SO hSO hSO
  TOp hTOp (-1) T f.
by rewrite scaleN1r in h.
Qed.

(** Source for [distribution_directional_derivative_continuous]:
    the directional partial differential operator is a continuous
    linear endomorphism of D' in its original weak topology,
    Federer 4.1.1, p. 346. *)
Theorem distribution_directional_derivative_continuous:
  open_family_continuous DO DO distribution_directional_derivative.
Proof. exact:continuous_real_dual_scaled_transpose_weak_continuous. Qed.
End DistributionDifferentiation.
