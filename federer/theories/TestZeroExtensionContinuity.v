(** Federer (1969), 4.1.1, p. 345: actual zero
    extension is continuous on fixed-support steps and
    on the literal final test topology. The original
    derivative seminorms give constant-one estimates. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import Hom RealNormUP NormDifferentialUP ContinuousMultilinearSealed ContinuousMultilinearNorm
  OpenFamilyTopologyUP FinalOpenTopologyUP DirectedSeminormFamilyUP SeminormFamilyRestriction SeminormFamilyLinearContinuity
  SmoothCompactSet SmoothCompactDomainInclusion SmoothFunctionSpaceUP SmoothFunctionSupport
  SmoothFunctionDerivativesUP SmoothDerivativeSeminormUP SmoothFunctionSeminormFamily SmoothFunctionTopology
  SmoothLocalSupport SmoothTestSpaces SmoothTestEvaluation SmoothTestTopology TestZeroExtensionUP
  TestZeroExtensionFixed TestZeroExtensionDerivatives LinearSubspaceRepresentationUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section TestExtensionContinuity.
Variable R:realType.
Variables X Y:lmodType R.
Variables (NX:X->R) (NY:Y->R).
Hypothesis hNX:is_real_norm NX.
Hypothesis hNY:is_real_norm NY.
Variables U V:X->Prop.
Hypothesis hU:forall x,U x ->norm_domain_interior NX U x.
Hypothesis hV:forall x,V x ->norm_domain_interior NX V x.
Hypothesis hUV:forall x,U x ->V x.
Variables A B:lmodType R.
Variable evA:A->X->Y.
Variable evB:B->X->Y.
Hypothesis hA:is_smooth_function_space hNX hNY U evA.
Hypothesis hB:is_smooth_function_space hNX hNY V evB.
Local Notation Z := (fun k=>@ContinuousMultilinear.space R k X Y NX NY hNX hNY).
Local Notation ZN := (fun k=>@ContinuousMultilinear.norm R k X Y NX NY hNX hNY).
Local Notation hZ := (fun k=>@ContinuousMultilinear.laws R k X Y NX NY hNX hNY).
Variables DA:forall k,X->Hom A (Z k).
Variables DB:forall k,X->Hom B (Z k).
Hypothesis hDA:@is_smooth_function_derivatives R X Y NX NY hNX hNY U A evA DA.
Hypothesis hDB:@is_smooth_function_derivatives R X Y NX NY hNX hNY V B evB DB.
Local Notation TA := (smooth_test_space hA).
Local Notation TB := (smooth_test_space hB).
Variable L:Hom TA TB.
Hypothesis hL:is_test_zero_extension U V (smooth_test_value hA) (smooth_test_value hB) L.
Local Notation IA := (nat*smooth_compact_set hNX U)%type.
Local Notation IB := (nat*smooth_compact_set hNX V)%type.
Local Notation nuA := (smooth_function_derivative_seminorm hDA).
Local Notation nuB := (smooth_function_derivative_seminorm hDB).

(** Source for [test_zero_extension_fixed_continuous]: the
    actual map D_K(U,Y) to D_K(V,Y)
    is continuous, supporting the homeomorphism in
    Federer 4.1.1, p. 345. *)
Theorem test_zero_extension_fixed_continuous (K:smooth_compact_set hNX U):
  open_family_continuous (smooth_test_step_opens hA hDA K)
    (smooth_test_step_opens hB hDB (@smooth_compact_domain_inclusion R X NX hNX U V hUV K))
    (@test_zero_extension_fixed R X Y NX NY hNX hNY U V hUV A B evA evB hA hB L hL K).
Proof.
pose KV:=@smooth_compact_domain_inclusion R X NX hNX U V hUV K.
pose AK:=smooth_fixed_test_space hA K.
pose BK:=smooth_fixed_test_space hB KV.
pose kA:=smooth_fixed_test_inclusion hA K.
pose kB:=smooth_fixed_test_inclusion hB KV.
pose P:=@test_zero_extension_fixed R X Y NX NY hNX hNY U V hUV A B evA evB hA hB L hL K.
pose p (i:IA) (f:AK):=nuA i.2 i.1 (kA f).
pose q (i:IB) (f:BK):=nuB i.2 i.1 (kB f).
have hp:is_directed_seminorm_family p:=restricted_seminorm_family_directed
  (smooth_function_seminorms_directed (smooth_function_derivative_seminorm_laws hDA)) kA.
apply:(@seminorm_family_bounded_linear_continuous R AK BK IA IB p q
  (smooth_test_step_opens hA hDA K) (smooth_test_step_opens hB hDB KV) hp
  (smooth_test_step_topology_laws hA hDA K) (smooth_test_step_topology_laws hB hDB KV) P).
move=>[i M]; exists (i,K),1; split; first exact:ler01.
move=>f; rewrite /p /q mul1r.
apply:(@smooth_derivative_seminorm_least R X Y NX NY hNX hNY V B DB M i (nuB M i)
  (smooth_function_derivative_seminorm_laws hDB M i) (kB (P f)) (nuA K i (kA f))
  (smooth_derivative_seminorm_nonnegative (smooth_function_derivative_seminorm_laws hDA K i) (kA f)))=>j hj x hx.
case:(pselect (smooth_compact_carrier K x))=>[hKx|hKx].
- rewrite (@test_zero_extension_fixed_evaluation R X Y NX NY hNX hNY U V hUV A B evA evB hA hB L hL K f)
    -(@test_zero_extension_higher_derivative R X Y NX NY hNX hNY U V hU hUV A B evA evB hA hB
      DA DB hDA hDB L hL j (smooth_test_step hA K f) x (smooth_compact_in_domain K x hKx))
    smooth_test_step_evaluation.
  exact:(smooth_derivative_seminorm_bound (smooth_function_derivative_seminorm_laws hDA K i) (kA f) hj hKx).
- have hSupport:@smooth_function_support R X Y NX hNX V B evB (kB (P f)) `<=` smooth_compact_carrier K.
    exact:(subspace_representation_member (smooth_fixed_test_space_laws hB KV) (P f)).
  have hNo:~@smooth_function_support R X Y NX hNX V B evB (kB (P f)) x.
    move=>hs; exact:hKx (hSupport x hs).
  rewrite (@smooth_derivative_outside_support R X Y NX NY hNX hNY V hV B evB DB hDB
    (kB (P f)) x (smooth_compact_in_domain M x hx) hNo j)
    (real_seminorm_zero (continuous_multilinear_norm_is_norm hNY (hZ j)).1).
  exact:(smooth_derivative_seminorm_nonnegative (smooth_function_derivative_seminorm_laws hDA K i) (kA f)).
Qed.

(** Source for [test_zero_extension_continuous]: the actual
    zero-extension monomorphism D(U,Y) to D(V,Y)
    is continuous for Federer's literal final topologies,
    Federer 4.1.1, p. 345. *)
Theorem test_zero_extension_continuous:
  open_family_continuous (smooth_test_opens hA hDA) (smooth_test_opens hB hDB) L.
Proof.
apply:(@final_open_topology_mapping (smooth_compact_set hNX U)
  (fun K=>smooth_fixed_test_space hA K) TA TB (smooth_test_step_opens hA hDA)
  (fun K f=>smooth_test_step hA K f) (smooth_test_opens hA hDA) (smooth_test_opens hB hDB) L
  (smooth_test_final_topology_laws hA hDA)).2=>K.
pose KV:=@smooth_compact_domain_inclusion R X NX hNX U V hUV K.
pose P:=@test_zero_extension_fixed R X Y NX NY hNX hNY U V hUV A B evA evB hA hB L hL K.
have he:(fun f=>L (smooth_test_step hA K f))=(fun f=>smooth_test_step hB KV (P f)).
  apply:funext=>f; symmetry.
  exact (@test_zero_extension_fixed_step_commutes R X Y NX NY hNX hNY U V hUV A B evA evB hA hB L hL K f).
rewrite he.
exact (@open_family_continuous_compose (smooth_fixed_test_space hA K) (smooth_fixed_test_space hB KV) TB
  (smooth_test_step_opens hA hDA K) (smooth_test_step_opens hB hDB KV) (smooth_test_opens hB hDB)
  P (smooth_test_step hB KV) (@test_zero_extension_fixed_continuous K)
  (@final_open_topology_inclusion (smooth_compact_set hNX V) (fun M=>smooth_fixed_test_space hB M)
    TB (smooth_test_step_opens hB hDB) (fun M f=>smooth_test_step hB M f) (smooth_test_opens hB hDB)
    (smooth_test_final_topology_laws hB hDB) KV)).
Qed.
End TestExtensionContinuity.
