(** Federer (1969), 4.1.1, p. 346: actual continuous
    differentiation on D_K(U,Y) and D(U,Y). Final-topology
    continuity is proved on the original fixed-support steps,
    without assuming joint vector continuity of D. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import Hom ModuleQuotient RealNormUP NormDifferentialUP ContinuousMultilinearSealed
  OpenFamilyTopologyUP InitialOpenTopologyUP FinalOpenTopologyUP LinearSubspaceRepresentationUP
  LinearSubspaceLiftSealed SmoothCompactSet SmoothFunctionSpaceUP SmoothFunctionDerivativesUP
  SmoothTestSubspaces SmoothTestSpaces SmoothTestTopology SmoothFunctionTopology
  SmoothDirectionalDerivativeUP SmoothDirectionalSupport SmoothDirectionalContinuity.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section TestDifferentiation.
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
Variable P:Hom E E.
Hypothesis hP:@is_smooth_directional_derivative R X Y NX NY hNX hNY U E ev D v P.
Local Notation KIndex := (smooth_compact_set hNX U).
Local Notation DK := (smooth_fixed_test_space hE).
Local Notation DT := (smooth_test_space hE).
Local Notation k := (smooth_fixed_test_inclusion hE).
Local Notation inc := (smooth_test_inclusion hE).
Local Notation j := (smooth_test_step hE).
Local Notation EO := (smooth_function_opens hD).
Local Notation PK := (smooth_test_step_opens hE hD).
Local Notation SO := (smooth_test_opens hE hD).

(** Source for [test_directional_fixed_member]: the derivative
    of a member of D_K remains in that same subspace, supporting
    the test operators of Federer 4.1.1, p. 346. *)
Lemma test_directional_fixed_member K (f:DK K):
  smooth_fixed_support_subspace hE K (hom_comp P (k K) f).
Proof.
apply:(smooth_directional_derivative_preserves_compact_support hU hE hD hP).
exact:subspace_representation_member (smooth_fixed_test_space_laws hE K) f.
Qed.

(** Source for [test_directional_fixed_operator]: the actual
    linear derivative on D_K(U,Y), supporting Federer 4.1.1,
    p. 346. Its corestriction is opaque. *)
Definition test_directional_fixed_operator K:Hom (DK K) (DK K):=
  @LinearSubspaceLift.map R (DK K) (DK K) E (smooth_fixed_support_subspace hE K)
    (k K) (smooth_fixed_test_space_laws hE K) (hom_comp P (k K))
    (fun f=>@test_directional_fixed_member K f).

(** Source for [test_directional_fixed_evaluation]: fixed-support
    differentiation preserves the original function derivative,
    supporting Federer 4.1.1, p. 346. *)
Lemma test_directional_fixed_evaluation K f:
  k K (test_directional_fixed_operator K f)= P (k K f).
Proof. exact:LinearSubspaceLift.evaluation. Qed.

(** Source for [test_directional_member]: the derivative of a
    compactly supported function is compactly supported, supporting
    D_j phi in Federer 4.1.1, p. 346. *)
Lemma test_directional_member f:
  smooth_compact_support_subspace hE (hom_comp P inc f).
Proof.
have [K hK]:=subspace_representation_member (smooth_test_space_laws hE) f.
exists K; exact:(smooth_directional_derivative_preserves_compact_support hU hE hD hP hK).
Qed.

(** Source for [test_directional_operator]: actual directional
    differentiation on D(U,Y), supporting the standard-coordinate
    operators in Federer 4.1.1, p. 346. *)
Definition test_directional_operator:Hom DT DT:=
  @LinearSubspaceLift.map R DT DT E (smooth_compact_support_subspace hE) inc
    (smooth_test_space_laws hE) (hom_comp P inc) test_directional_member.

(** Source for [test_directional_evaluation]: differentiation
    on D agrees with differentiation of its actual smooth
    function, supporting Federer 4.1.1, p. 346. *)
Lemma test_directional_evaluation f:
  inc (test_directional_operator f)= P (inc f).
Proof. exact:LinearSubspaceLift.evaluation. Qed.

(** Source for [test_directional_step_commutes]: differentiating
    before or after fixed-step inclusion gives the same test
    function, supporting Federer 4.1.1, p. 346. *)
Lemma test_directional_step_commutes K f:
  test_directional_operator (j K f)=j K (test_directional_fixed_operator K f).
Proof.
apply:(subspace_representation_injective (smooth_test_space_laws hE)).
by rewrite test_directional_evaluation !smooth_test_step_evaluation test_directional_fixed_evaluation.
Qed.

(** Source for [test_directional_fixed_continuous]: the derivative
    on each D_K is continuous for its original E-relative
    topology, supporting Federer 4.1.1, p. 346. *)
Theorem test_directional_fixed_continuous K:
  open_family_continuous (PK K) (PK K) (test_directional_fixed_operator K).
Proof.
have hRel:=@smooth_test_step_relative_topology R X Y NX NY hNX hNY U E ev hE D hD K.
apply:(@initial_open_topology_mapping (DK K) E (DK K) EO (k K) (PK K)
  (PK K) (test_directional_fixed_operator K) hRel).2.
have he:(fun f:DK K=>k K (test_directional_fixed_operator K f))=(fun f=>P (k K f)).
  apply:funext=>f; exact:test_directional_fixed_evaluation.
rewrite he.
have hInc:open_family_continuous (PK K) EO (k K):=initial_open_topology_inclusion hRel.
have hDer:open_family_continuous EO EO P:=
  @smooth_directional_derivative_continuous R X Y NX NY hNX hNY U hU E ev D hD v P hP.
exact (@open_family_continuous_compose (DK K) E E (PK K) EO EO (k K) P hInc hDer).
Qed.

(** Source for [test_directional_operator_continuous]: the
    actual derivative is continuous for Federer's literal final
    topology on D, supporting the distribution differential
    endomorphisms of Federer 4.1.1, p. 346. *)
Theorem test_directional_operator_continuous:
  open_family_continuous SO SO test_directional_operator.
Proof.
have hFinal:=smooth_test_final_topology_laws hE hD.
apply:(@final_open_topology_mapping KIndex (fun K=>DK K) DT DT PK (fun K f=>j K f)
  SO SO test_directional_operator hFinal).2=>K.
have he:(fun f:DK K=>test_directional_operator (j K f))=
    (fun f=>j K (test_directional_fixed_operator K f)).
  apply:funext=>f; exact:test_directional_step_commutes.
rewrite he.
exact (@open_family_continuous_compose (DK K) (DK K) DT (PK K) (PK K) SO
  (test_directional_fixed_operator K) (j K) (@test_directional_fixed_continuous K)
  (@final_open_topology_inclusion KIndex (fun K=>DK K) DT PK (fun K f=>j K f) SO hFinal K)).
Qed.
End TestDifferentiation.
