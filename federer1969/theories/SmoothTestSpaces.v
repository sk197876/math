(** Federer (1969), 4.1.1, pp. 344–345: actual fixed-support
    and test-function spaces. Their independently specified
    support subspaces are represented through the existing opaque
    subspace model; corestriction uses only its exact image laws. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals.
From Federer Require Import Hom ModuleQuotient RealNormUP SmoothCompactSet SmoothFunctionSpaceUP
  SmoothFunctionSupport SmoothTestSubspaces LinearSubspaceRepresentationUP
  LinearSubspaceRepresentationSealed LinearSubspaceLiftSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section TestFunctionSpaces.
Variable R:realType.
Variables X Y:lmodType R.
Variables (NX:X->R) (NY:Y->R).
Hypothesis hNX:is_real_norm NX.
Hypothesis hNY:is_real_norm NY.
Variable U:set X.
Variable E:lmodType R.
Variable ev:E->X->Y.
Hypothesis hE:is_smooth_function_space hNX hNY U ev.
Local Notation KIndex := (smooth_compact_set hNX U).

(** Source for [smooth_fixed_test_space]: D_K(U,Y), the
    smooth functions supported in K, Federer 4.1.1, p. 344. *)
Definition smooth_fixed_test_space (K:KIndex):lmodType R:=
  @LinearSubspaceRepresentation.space R E (smooth_fixed_support_subspace hE K).

(** Source for [smooth_fixed_test_inclusion]: the injective
    linear inclusion of D_K in E, Federer 4.1.1, p. 344. *)
Definition smooth_fixed_test_inclusion (K:KIndex):Hom (smooth_fixed_test_space K) E:=
  @LinearSubspaceRepresentation.inclusion R E (smooth_fixed_support_subspace hE K).

(** Source for [smooth_fixed_test_space_laws]: the image is
    exactly the functions with support in K, Federer 4.1.1, p. 344. *)
Lemma smooth_fixed_test_space_laws K:
  is_linear_subspace_representation (smooth_fixed_support_subspace hE K)
    (smooth_fixed_test_inclusion K).
Proof. exact:LinearSubspaceRepresentation.laws. Qed.

(** Source for [smooth_test_space]: D(U,Y), the union of the
    compact-support subspaces, Federer 4.1.1, p. 344. *)
Definition smooth_test_space:lmodType R:=
  @LinearSubspaceRepresentation.space R E (smooth_compact_support_subspace hE).

(** Source for [smooth_test_inclusion]: the actual linear
    injection from D(U,Y) to E(U,Y), Federer 4.1.1, p. 344. *)
Definition smooth_test_inclusion:Hom smooth_test_space E:=
  @LinearSubspaceRepresentation.inclusion R E (smooth_compact_support_subspace hE).

(** Source for [smooth_test_space_laws]: the exact image consists
    of all compactly supported smooth functions, Federer 4.1.1,
    pp. 344–345. *)
Lemma smooth_test_space_laws:
  is_linear_subspace_representation (smooth_compact_support_subspace hE)
    smooth_test_inclusion.
Proof. exact:LinearSubspaceRepresentation.laws. Qed.

(** Source for [smooth_fixed_test_is_test]: a function supported
    in a fixed K has compact support, supporting the union defining
    D(U,Y), Federer 4.1.1, p. 344. *)
Lemma smooth_fixed_test_is_test K (f:smooth_fixed_test_space K):
  smooth_compact_support_subspace hE (smooth_fixed_test_inclusion K f).
Proof.
exists K; exact:(subspace_representation_member (smooth_fixed_test_space_laws K) f).
Qed.

(** Source for [smooth_test_step]: the original linear inclusion
    from D_K(U,Y) to D(U,Y), Federer 4.1.1, p. 344. *)
Definition smooth_test_step K:Hom (smooth_fixed_test_space K) smooth_test_space:=
  @LinearSubspaceLift.map R (smooth_fixed_test_space K) smooth_test_space E
    (smooth_compact_support_subspace hE) smooth_test_inclusion smooth_test_space_laws
    (smooth_fixed_test_inclusion K) (fun f=>smooth_fixed_test_is_test f).

(** Source for [smooth_test_step_evaluation]: the inclusion
    preserves the underlying function, Federer 4.1.1, p. 344. *)
Lemma smooth_test_step_evaluation K f:
  smooth_test_inclusion (smooth_test_step K f)=smooth_fixed_test_inclusion K f.
Proof. exact:LinearSubspaceLift.evaluation. Qed.

(** Source for [smooth_test_step_injective]: each fixed-support
    inclusion is injective, supporting Federer 4.1.1, p. 344. *)
Lemma smooth_test_step_injective K:injective (smooth_test_step K).
Proof.
move=>f g he; apply:(subspace_representation_injective (smooth_fixed_test_space_laws K)).
by rewrite -!smooth_test_step_evaluation he.
Qed.

(** Source for [smooth_test_steps_cover]: every test function
    belongs to one fixed-support step, the union assertion in
    Federer 4.1.1, p. 344. *)
Theorem smooth_test_steps_cover f:
  exists K,exists g:smooth_fixed_test_space K,smooth_test_step K g=f.
Proof.
have [K hK]:=subspace_representation_member smooth_test_space_laws f.
have [g hg]:=subspace_representation_full (smooth_fixed_test_space_laws K) hK.
exists K,g; apply:(subspace_representation_injective smooth_test_space_laws).
by rewrite smooth_test_step_evaluation hg.
Qed.
End TestFunctionSpaces.
