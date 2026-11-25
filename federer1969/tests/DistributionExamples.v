(** Federer (1969), 4.1.1, pp. 343–346: boundary
    regressions retain empty domains and derivative degree
    zero. The concrete noncompact-support distribution and
    zero-dimensional nonembedding counterexample are also
    imported through the public interface. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import Hom RealNormUP NormDifferentialUP ContinuousMultilinearSealed
  SmoothFunctionSpaceUP SmoothFunctionDerivativesUP SmoothTestSpaces SmoothTestEvaluation SmoothTestTopology
  ContinuousRealDual LinearSubspaceRepresentationUP DistributionIteratedDerivative Distributions.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section DistributionBoundaryRegression.
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

(** Source for [distribution_degree_zero_regression]: derivative
    order zero is the identity on every actual distribution,
    including empty domains, supporting the multiindex
    convention in Federer 4.1.1, p. 346. *)
Theorem distribution_degree_zero_regression (T:DD):
  @distribution_iterated_derivative R X Y NX NY hNX hNY U hU E ev hE D hD [::] T=T.
Proof.
apply:(subspace_representation_injective (@continuous_real_dual_model_laws R DT SO hSO)).
apply:hom_ext=>f.
rewrite distribution_iterated_derivative_evaluation /= scale1r.
reflexivity.
Qed.
End DistributionBoundaryRegression.

Section EmptyDomainRegression.
Variable R:realType.
Variables X Y:lmodType R.
Variables (NX:X->R) (NY:Y->R).
Hypothesis hNX:is_real_norm NX.
Hypothesis hNY:is_real_norm NY.

(** Source for [empty_distribution_domain_open]: the empty
    domain meets the original openness hypothesis,
    Federer 4.1.1, p. 343. *)
Lemma empty_distribution_domain_open x:
  (@set0 X) x ->norm_domain_interior NX set0 x.
Proof. by []. Qed.
Local Notation hEmpty := empty_distribution_domain_open.
Local Notation E := (@distribution_smooth_space R X Y NX NY hNX hNY set0 hEmpty).
Local Notation ev := (@distribution_smooth_value R X Y NX NY hNX hNY set0 hEmpty).
Local Notation hE := (@distribution_smooth_laws R X Y NX NY hNX hNY set0 hEmpty).
Local Notation DT := (@distribution_test_space R X Y NX NY hNX hNY set0 hEmpty).

(** Source for [empty_domain_test_space_regression]: every
    member of the actual test-function space on the
    empty open domain is zero, supporting the boundary
    case in Federer 4.1.1, p. 344. *)
Theorem empty_domain_test_space_regression (f:DT):f=0.
Proof. apply:(smooth_test_values_extensional hE); by move=>x hx. Qed.
End EmptyDomainRegression.
