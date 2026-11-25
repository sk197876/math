(** Federer (1969), 4.1.1, p. 346: the
    original symmetric multiindices specify partial
    differential operators with sign (-1)^i.
    Coordinate bases give exactly the printed D^alpha. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals.
From Federer Require Import Hom RealNormUP NormDifferentialUP ContinuousMultilinearSealed
  SymmetricMultiIndices SymmetricIndexBounds SymmetricMonomialTuples OpenFamilyTopologyUP
  SmoothFunctionSpaceUP SmoothFunctionDerivativesUP SmoothTestSpaces SmoothTestTopology
  ContinuousRealDual DistributionIteratedDerivative TestIteratedDerivativeIdentification.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Section DistributionMultiindex.
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
Variable n:nat.
Variable b:'I_n->X.
Local Notation DT := (smooth_test_space hE).
Local Notation SO := (smooth_test_opens hE hD).
Local Notation hSO := (smooth_test_final_topology_laws hE hD).1.
Local Notation DD := (@continuous_real_dual_space R DT SO hSO).
Local Notation e := (@continuous_real_dual_evaluation R DT SO hSO).
Local Notation DO := (@continuous_real_dual_weak_opens R DT SO hSO).
Local Notation Q := (@distribution_test_iterated_derivative R X Y NX NY hNX hNY U hU E ev hE D hD).
Local Notation M := (@distribution_iterated_derivative R X Y NX NY hNX hNY U hU E ev hE D hD).

(** Source for [distribution_multiindex_derivative]: D^alpha
    on the original weak distribution dual, using
    the repeated basis factors of alpha from
    Chapter 1, Federer 4.1.1, p. 346. *)
Definition distribution_multiindex_derivative i (alpha:symmetric_indices n i):Hom DD DD:=
  M (symmetric_monomial_tuple b alpha).

(** Source for [distribution_multiindex_derivative_evaluation]:
    D^alpha T=(-1)^i TD^alpha, the original
    formula in Federer 4.1.1, p. 346. *)
Theorem distribution_multiindex_derivative_evaluation i (alpha:symmetric_indices n i) T f:
  e (distribution_multiindex_derivative alpha T) f=
    ((-1)^+i)*:e T (Q (symmetric_monomial_tuple b alpha) f).
Proof.
rewrite /distribution_multiindex_derivative distribution_iterated_derivative_evaluation size_tuple.
reflexivity.
Qed.

(** Source for [distribution_multiindex_derivative_continuous]:
    every original multiindex partial operator is
    weakly continuous and linear, Federer 4.1.1,
    p. 346. *)
Theorem distribution_multiindex_derivative_continuous i (alpha:symmetric_indices n i):
  open_family_continuous DO DO (distribution_multiindex_derivative alpha).
Proof. exact:distribution_iterated_derivative_continuous. Qed.
End DistributionMultiindex.
