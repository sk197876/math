(** Federer (1969), 4.1.1, pp. 343–346: public
    smooth functions, compact tests and real distributions.
    Implementations remain behind their opaque interfaces.
    The literal final test topology and the locally convex
    topology have the same continuous linear maps into
    locally convex spaces; they are not identified. *)
From mathcomp Require Import all_boot all_order all_algebra reals classical_sets.
From Federer Require Export SmoothFunctionSpaceSealed SmoothFunctionDerivativesSealed SmoothFunctionTopology
  SmoothTestLocallyConvexTopology SmoothTestDensity
  SmoothFixedSupportClosed SmoothTestEvaluation SmoothTestTopology
  InductiveLimitTopologyMapping SmoothTestNonembedding ZeroDimensionalTestTopologyCounterexample
  SmoothDualFiniteBound SmoothDualFunctionalSupport SmoothDualFixedSupportClosed
  SmoothDualSequenceCommonSupport SmoothDualCompactImage SmoothDualFixedSupportEmbedding
  DistributionLocalBound DistributionFixedSupportClosed TestZeroExtensionFixedHomeomorphism
  DistributionOpenRestriction DistributionPartition DistributionDirectionalDerivative
  DistributionMultiindexDerivative TestMultiindexDerivativeIdentification DistributionQuotientFormula
  DistributionFromDualFieldSealed DistributionIntegralByParts EuclideanDistributionMeasureContext
  NoncompactDistributionSupportExample.
From Federer Require Import Hom RealNormUP NormDifferentialUP SmoothFunctionSpaceUP SmoothFunctionDerivativesUP
  SmoothTestSpaces ContinuousRealDual WeakEvaluationTopologySealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Section DistributionSpaces.
Variable R:realType.
Variables X Y:lmodType R.
Variables (NX:X->R) (NY:Y->R).
Hypothesis hNX:is_real_norm NX.
Hypothesis hNY:is_real_norm NY.
Variable U:set X.
Hypothesis hU:forall x,U x ->norm_domain_interior NX U x.

(** Source for [distribution_smooth_space]: E(U,Y), the
    original smooth-function space of Federer 4.1.1,
    p. 343, specified independently before its existence. *)
Definition distribution_smooth_space:lmodType R:=
  @SmoothFunctionSpace.space R X Y NX NY hNX hNY U hU.

(** Source for [distribution_smooth_value]: evaluation of
    E(U,Y), Federer 4.1.1, p. 343. *)
Definition distribution_smooth_value:distribution_smooth_space->X->Y:=
  @SmoothFunctionSpace.value R X Y NX NY hNX hNY U hU.

(** Source for [distribution_smooth_laws]: the original
    smoothness, extensionality, linearity and realization
    laws for E(U,Y), Federer 4.1.1, p. 343. *)
Lemma distribution_smooth_laws:
  is_smooth_function_space hNX hNY U distribution_smooth_value.
Proof. exact:SmoothFunctionSpace.laws. Qed.

(** Source for [distribution_smooth_derivatives]: the exact
    higher derivatives on E(U,Y), Federer 4.1.1,
    pp. 343–344. Their existence precedes opaque sealing. *)
Definition distribution_smooth_derivatives:=
  @SmoothFunctionDerivatives.operators R X Y NX NY hNX hNY U
    distribution_smooth_space distribution_smooth_value distribution_smooth_laws.

(** Source for [distribution_smooth_derivative_laws]: the
    supplied higher derivatives satisfy their independent
    original laws, Federer 4.1.1, pp. 343–344. *)
Lemma distribution_smooth_derivative_laws:
  @is_smooth_function_derivatives R X Y NX NY hNX hNY U
    distribution_smooth_space distribution_smooth_value distribution_smooth_derivatives.
Proof. exact:SmoothFunctionDerivatives.laws. Qed.

(** Source for [distribution_test_space]: D(U,Y), the
    compactly supported smooth functions, Federer 4.1.1,
    pp. 344–345. *)
Definition distribution_test_space:lmodType R:=smooth_test_space distribution_smooth_laws.

(** Source for [distribution_test_value]: original test
    evaluation, Federer 4.1.1, pp. 344–345. *)
Definition distribution_test_value:distribution_test_space->X->Y:=
  smooth_test_value distribution_smooth_laws.

(** Source for [distribution_test_opens]: Federer's literal
    final topology on D(U,Y), 4.1.1, p. 344.
    No joint vector continuity is asserted for it. *)
Definition distribution_test_opens:=
  smooth_test_opens distribution_smooth_laws distribution_smooth_derivative_laws.

(** Source for [distribution_test_topology_laws]: openness
    in D(U,Y) is tested on each fixed compact-support
    step, Federer 4.1.1, p. 344. *)
Definition distribution_test_topology_laws:=
  smooth_test_final_topology_laws distribution_smooth_laws distribution_smooth_derivative_laws.

(** Source for [distribution_space]: D'(U,Y), the original
    continuous real dual of the test space,
    Federer 4.1.1, p. 345. *)
Definition distribution_space:lmodType R:=
  @continuous_real_dual_space R distribution_test_space distribution_test_opens
    distribution_test_topology_laws.1.

(** Source for [distribution_value]: T(phi), the original
    real evaluation of a distribution, Federer 4.1.1,
    p. 345. *)
Definition distribution_value:Hom distribution_space (Hom distribution_test_space R^o):=
  @continuous_real_dual_evaluation R distribution_test_space distribution_test_opens
    distribution_test_topology_laws.1.

(** Source for [distribution_weak_opens]: the weak topology
    specified by the original evaluation strips,
    Federer 4.1.1, p. 345. *)
Definition distribution_weak_opens:=
  @WeakEvaluationTopology.opens R distribution_test_space distribution_space (fun T f=>distribution_value T f).
End DistributionSpaces.
