(** Federer (1969), 4.1.7, pp. 355–356: local
    continuous smooth operators induce continuous maps
    on the original compact tests. The proof passes
    through fixed-support steps of 4.1.1, p. 344;
    no joint vector continuity of the final topology
    is assumed. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import Hom ModuleQuotient RealNormUP ContinuousMultilinearSealed
  OpenFamilyTopologyUP InitialOpenTopologyUP FinalOpenTopologyUP LinearSubspaceRepresentationUP
  LinearSubspaceLiftSealed SmoothCompactSet SmoothFunctionSpaceUP SmoothFunctionSupport
  SmoothFunctionDerivativesUP SmoothTestSubspaces SmoothTestSpaces SmoothTestTopology
  SmoothFunctionTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Section SupportedSmoothOperatorTests.
Variable R:realType.
Variables X Y Z:lmodType R.
Variables (NX:X->R) (NY:Y->R) (NZ:Z->R).
Hypotheses (hNX:is_real_norm NX) (hNY:is_real_norm NY) (hNZ:is_real_norm NZ).
Variable U:set X.
Variables E F:lmodType R.
Variables (ev:E->X->Y) (fv:F->X->Z).
Hypothesis hE:is_smooth_function_space hNX hNY U ev.
Hypothesis hF:is_smooth_function_space hNX hNZ U fv.
Local Notation Pjet := (fun j=>@ContinuousMultilinear.space R j X Y NX NY hNX hNY).
Local Notation Qjet := (fun j=>@ContinuousMultilinear.space R j X Z NX NZ hNX hNZ).
Variable D:forall j,X->Hom E (Pjet j).
Variable G:forall j,X->Hom F (Qjet j).
Hypothesis hD:@is_smooth_function_derivatives R X Y NX NY hNX hNY U E ev D.
Hypothesis hG:@is_smooth_function_derivatives R X Z NX NZ hNX hNZ U F fv G.
Variable P:Hom E F.
Hypothesis hSupport:forall (K:smooth_compact_set hNX U) f,
  @smooth_function_support R X Y NX hNX U E ev f `<=` smooth_compact_carrier K ->
  @smooth_function_support R X Z NX hNX U F fv (P f) `<=` smooth_compact_carrier K.
Local Notation DE := (smooth_test_space hE).
Local Notation DF := (smooth_test_space hF).
Local Notation DKE := (smooth_fixed_test_space hE).
Local Notation DKF := (smooth_fixed_test_space hF).
Local Notation iE := (smooth_test_inclusion hE).
Local Notation iF := (smooth_test_inclusion hF).
Local Notation kE := (smooth_fixed_test_inclusion hE).
Local Notation kF := (smooth_fixed_test_inclusion hF).
Local Notation jE := (smooth_test_step hE).
Local Notation jF := (smooth_test_step hF).
Local Notation EO := (smooth_function_opens hD).
Local Notation FO := (smooth_function_opens hG).
Local Notation PE := (smooth_test_step_opens hE hD).
Local Notation PF := (smooth_test_step_opens hF hG).
Local Notation SE := (smooth_test_opens hE hD).
Local Notation SF := (smooth_test_opens hF hG).

(** Source for [supported_smooth_fixed_member]: the
    original operator preserves D_K, supporting the
    current operations of Federer 4.1.7, pp. 355–356. *)
Lemma supported_smooth_fixed_member K (f:DKE K):
  smooth_fixed_support_subspace hF K (hom_comp P (kE K) f).
Proof.
apply:hSupport.
exact:subspace_representation_member (smooth_fixed_test_space_laws hE K) f.
Qed.

(** Source for [supported_smooth_fixed_operator]: actual
    restriction to a fixed-support step, supporting
    Federer 4.1.7, pp. 355–356. *)
Definition supported_smooth_fixed_operator K:Hom (DKE K) (DKF K):=
  @LinearSubspaceLift.map R (DKE K) (DKF K) F (smooth_fixed_support_subspace hF K)
    (kF K) (smooth_fixed_test_space_laws hF K) (hom_comp P (kE K))
    (fun f=>@supported_smooth_fixed_member K f).

(** Source for [supported_smooth_fixed_evaluation]: exact
    inclusion equation on D_K, supporting Federer
    4.1.7, pp. 355–356. *)
Lemma supported_smooth_fixed_evaluation K f:
  kF K (supported_smooth_fixed_operator K f)= P (kE K f).
Proof. exact:LinearSubspaceLift.evaluation. Qed.

(** Source for [supported_smooth_test_member]: every
    actual compact test has an actual compact-test
    image, supporting Federer 4.1.7, pp. 355–356. *)
Lemma supported_smooth_test_member f:
  smooth_compact_support_subspace hF (hom_comp P iE f).
Proof.
have [K hK]:=subspace_representation_member (smooth_test_space_laws hE) f.
exists K; exact:hSupport K (iE f) hK.
Qed.

(** Source for [supported_smooth_test_operator]: actual
    operator on the original D spaces, supporting
    Federer 4.1.7, pp. 355–356. Its range lift
    uses the earlier opaque subspace interface. *)
Definition supported_smooth_test_operator:Hom DE DF:=
  @LinearSubspaceLift.map R DE DF F (smooth_compact_support_subspace hF) iF
    (smooth_test_space_laws hF) (hom_comp P iE) supported_smooth_test_member.

(** Source for [supported_smooth_test_evaluation]: exact
    action on the original underlying smooth function,
    supporting Federer 4.1.7, pp. 355–356. *)
Lemma supported_smooth_test_evaluation f:
  iF (supported_smooth_test_operator f)= P (iE f).
Proof. exact:LinearSubspaceLift.evaluation. Qed.

(** Source for [supported_smooth_step_commutes]: fixed
    step inclusion commutes with the actual operator,
    supporting Federer 4.1.7, pp. 355–356. *)
Lemma supported_smooth_step_commutes K f:
  supported_smooth_test_operator (jE K f)=jF K (supported_smooth_fixed_operator K f).
Proof.
apply:(subspace_representation_injective (smooth_test_space_laws hF)).
by rewrite supported_smooth_test_evaluation !smooth_test_step_evaluation supported_smooth_fixed_evaluation.
Qed.

Hypothesis hP:open_family_continuous EO FO P.

(** Source for [supported_smooth_fixed_continuous]: each
    fixed-support map is continuous for its original
    relative E topology, supporting Federer 4.1.7,
    pp. 355–356. *)
Theorem supported_smooth_fixed_continuous K:
  open_family_continuous (PE K) (PF K) (supported_smooth_fixed_operator K).
Proof.
have hRel:=@smooth_test_step_relative_topology R X Z NX NZ hNX hNZ U F fv hF G hG K.
apply:(@initial_open_topology_mapping (DKF K) F (DKE K) FO (kF K) (PF K)
  (PE K) (supported_smooth_fixed_operator K) hRel).2.
have he:(fun f:DKE K=>kF K (supported_smooth_fixed_operator K f))=(fun f=>P (kE K f)).
  apply:funext=>f; exact:supported_smooth_fixed_evaluation.
rewrite he.
have hInc:open_family_continuous (PE K) EO (kE K):=
  initial_open_topology_inclusion
    (@smooth_test_step_relative_topology R X Y NX NY hNX hNY U E ev hE D hD K).
exact:(open_family_continuous_compose hInc hP).
Qed.

(** Source for [supported_smooth_test_continuous]: the
    actual test operator is continuous for Federer's
    literal final topology, supporting Federer 4.1.7,
    pp. 355–356. No locally convex replacement is used. *)
Theorem supported_smooth_test_continuous:
  open_family_continuous SE SF supported_smooth_test_operator.
Proof.
have hFinal:=smooth_test_final_topology_laws hE hD.
apply:(@final_open_topology_mapping (smooth_compact_set hNX U) (fun K=>DKE K) DE DF PE
  (fun K f=>jE K f) SE SF supported_smooth_test_operator hFinal).2=>K.
have he:(fun f:DKE K=>supported_smooth_test_operator (jE K f))=
    (fun f=>jF K (supported_smooth_fixed_operator K f)).
  apply:funext=>f; exact:supported_smooth_step_commutes.
rewrite he.
have hInc:open_family_continuous (PF K) SF (jF K):=
  @final_open_topology_inclusion (smooth_compact_set hNX U) (fun K=>DKF K) DF PF
    (fun K f=>jF K f) SF (smooth_test_final_topology_laws hF hG) K.
exact:(open_family_continuous_compose (@supported_smooth_fixed_continuous K) hInc).
Qed.
End SupportedSmoothOperatorTests.
