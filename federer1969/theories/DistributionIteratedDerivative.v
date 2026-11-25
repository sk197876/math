(** Federer (1969), 4.1.1, p. 346: multiindex
    derivatives of distributions have sign (-1)^i
    and are weakly continuous linear endomorphisms.
    Test derivatives are actual finite compositions
    of the already proved directional operators. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals.
From Federer Require Import Hom TensorUP RealNormUP NormDifferentialUP ContinuousMultilinearSealed
  OpenFamilyTopologyUP SmoothFunctionSpaceUP SmoothFunctionDerivativesUP
  SmoothDirectionalDerivativeSealed SmoothTestSpaces SmoothTestTopology TestDirectionalOperator
  ContinuousRealDual ContinuousRealDualScaledTranspose DistributionDirectionalDerivative.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section IteratedDistributionDerivative.
Variable R:realType.
Variables X Y:lmodType R.
Variables (NX:X->R) (NY:Y->R).
Hypothesis hNX:is_real_norm NX.
Hypothesis hNY:is_real_norm NY.
Variable U:X->Prop.
Hypothesis hU:forall x,U x ->norm_domain_interior NX U x.
Variable E:lmodType R.
Variable ev:E->X->Y.
Hypothesis hE:is_smooth_function_space hNX hNY U ev.
Local Notation Z := (fun k=>@ContinuousMultilinear.space R k X Y NX NY hNX hNY).
Variable D:forall k,X->Hom E (Z k).
Hypothesis hD:@is_smooth_function_derivatives R X Y NX NY hNX hNY U E ev D.
Local Notation DT := (smooth_test_space hE).
Local Notation SO := (smooth_test_opens hE hD).
Local Notation hSO := (smooth_test_final_topology_laws hE hD).1.
Local Notation DD := (@continuous_real_dual_space R DT SO hSO).
Local Notation e := (@continuous_real_dual_evaluation R DT SO hSO).
Local Notation DO := (@continuous_real_dual_weak_opens R DT SO hSO).
Local Notation Q := (fun v=>@distribution_test_directional_derivative R X Y NX NY hNX hNY U hU E ev hE D hD v).

(** Source for [distribution_test_iterated_derivative]: actual
    ordered differentiation of tests before duality,
    supporting TD^alpha in Federer 4.1.1, p. 346. *)
Fixpoint distribution_test_iterated_derivative (s:seq X):Hom DT DT:=
  if s is v::t then hom_comp (Q v) (distribution_test_iterated_derivative t)
  else hom_of_linear (linear_id DT).

(** Source for [distribution_test_iterated_continuous]: every
    finite test derivative is continuous for the
    original final topology, supporting the partial
    differential operators in Federer 4.1.1, p. 346. *)
Lemma distribution_test_iterated_continuous s:
  open_family_continuous SO SO (distribution_test_iterated_derivative s).
Proof.
elim:s=>[|v s ih]; first exact:open_family_continuous_identity.
exact:(open_family_continuous_compose ih
  (@test_directional_operator_continuous R X Y NX NY hNX hNY U hU E ev hE D hD v
    (@SmoothDirectionalDerivative.operator R X Y NX NY hNX hNY U E ev hE D hD v)
    (@SmoothDirectionalDerivative.laws R X Y NX NY hNX hNY U E ev hE D hD v))).
Qed.

(** Source for [distribution_iterated_derivative]: D^alpha T
    is (-1)^i times TD^alpha, the definition
    in Federer 4.1.1, p. 346. A
    direction list has degree equal to its length. *)
Definition distribution_iterated_derivative (s:seq X):Hom DD DD:=
  @continuous_real_dual_scaled_transpose R DT DT SO SO hSO hSO
    (distribution_test_iterated_derivative s) (distribution_test_iterated_continuous s)
    ((-1)^+(size s)).

(** Source for [distribution_iterated_derivative_evaluation]:
    the original (-1)^i evaluation formula for
    every finite ordered derivative, Federer 4.1.1,
    p. 346. *)
Theorem distribution_iterated_derivative_evaluation s T f:
  e (distribution_iterated_derivative s T) f=
    ((-1)^+(size s))*:e T (distribution_test_iterated_derivative s f).
Proof. exact:continuous_real_dual_scaled_transpose_evaluation. Qed.

(** Source for [distribution_iterated_derivative_continuous]:
    every finite partial differential operator is
    a weakly continuous linear endomorphism of
    D', Federer 4.1.1, p. 346. *)
Theorem distribution_iterated_derivative_continuous s:
  open_family_continuous DO DO (distribution_iterated_derivative s).
Proof. exact:continuous_real_dual_scaled_transpose_weak_continuous. Qed.
End IteratedDistributionDerivative.
