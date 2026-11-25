(** Federer (1969), 4.1.8, pp. 360–361: fixed-factor
    separated-test operators are continuous on the literal
    final test topologies. This supporting mapping lemma
    reuses the original relative support steps of 4.1.1,
    pp. 344–345, even when the two domains differ. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import Hom ModuleQuotient RealNormUP ContinuousMultilinearSealed
  SmoothFunctionSpaceUP SmoothFunctionDerivativesUP SmoothFunctionTopology
  SmoothFunctionSupport SmoothCompactSet SmoothTestSubspaces SmoothTestSpaces SmoothTestTopology
  LinearSubspaceRepresentationUP LinearSubspaceLiftSealed
  OpenFamilyTopologyUP InitialOpenTopologyUP FinalOpenTopologyUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Section SmoothTestOperatorBetweenDomains.
Variable R:realType.
Variables X1 X2 Y1 Y2:lmodType R.
Variables (NX1:X1->R) (NX2:X2->R) (NY1:Y1->R) (NY2:Y2->R).
Hypothesis hNX1:is_real_norm NX1.
Hypothesis hNX2:is_real_norm NX2.
Hypothesis hNY1:is_real_norm NY1.
Hypothesis hNY2:is_real_norm NY2.
Variables (U1:set X1) (U2:set X2).
Variables E1 E2:lmodType R.
Variables (ev1:E1->X1->Y1) (ev2:E2->X2->Y2).
Hypothesis hE1:is_smooth_function_space hNX1 hNY1 U1 ev1.
Hypothesis hE2:is_smooth_function_space hNX2 hNY2 U2 ev2.
Local Notation J1 := (fun k=>@ContinuousMultilinear.space R k X1 Y1 NX1 NY1 hNX1 hNY1).
Local Notation J2 := (fun k=>@ContinuousMultilinear.space R k X2 Y2 NX2 NY2 hNX2 hNY2).
Variable D1:forall k,X1->Hom E1 (J1 k).
Variable D2:forall k,X2->Hom E2 (J2 k).
Hypothesis hD1:@is_smooth_function_derivatives R X1 Y1 NX1 NY1 hNX1 hNY1 U1 E1 ev1 D1.
Hypothesis hD2:@is_smooth_function_derivatives R X2 Y2 NX2 NY2 hNX2 hNY2 U2 E2 ev2 D2.
Local Notation T1 := (smooth_test_space hE1).
Local Notation T2 := (smooth_test_space hE2).
Local Notation inc1 := (smooth_test_inclusion hE1).
Local Notation inc2 := (smooth_test_inclusion hE2).
Variable L:Hom T1 T2.
Variable P:Hom E1 E2.
Hypothesis hInclude:forall f,inc2 (L f) = P (inc1 f).
Hypothesis hContinuous:open_family_continuous
  (smooth_function_opens hD1) (smooth_function_opens hD2) P.

(** Source for [smooth_test_operator_between_fixed_steps]:
    a smooth continuous operator inducing a test map
    is continuous from each original support step into
    any fixed support step containing its image, supporting
    Federer 4.1.8, pp. 360–361, by the relative
    topologies of 4.1.1, pp. 344–345. *)
Theorem smooth_test_operator_between_fixed_steps
    (K:smooth_compact_set hNX1 U1) (M:smooth_compact_set hNX2 U2):
  (forall f:smooth_fixed_test_space hE1 K,
    @smooth_function_support R X2 Y2 NX2 hNX2 U2 E2 ev2
      (inc2 (L (smooth_test_step hE1 K f))) `<=` smooth_compact_carrier M)->
  open_family_continuous (smooth_test_step_opens hE1 hD1 K)
    (smooth_test_opens hE2 hD2) (fun f=>L (smooth_test_step hE1 K f)).
Proof.
move=>hBound.
pose DK:=smooth_fixed_test_space hE1 K.
pose DM:=smooth_fixed_test_space hE2 M.
pose k1:=smooth_fixed_test_inclusion hE1 K.
pose k2:=smooth_fixed_test_inclusion hE2 M.
pose raw:=hom_comp P k1.
have hMember f:smooth_fixed_support_subspace hE2 M (raw f).
  have h:=hBound f.
  by rewrite hInclude smooth_test_step_evaluation in h.
pose lift:=@LinearSubspaceLift.map R DK DM E2
  (smooth_fixed_support_subspace hE2 M) k2 (smooth_fixed_test_space_laws hE2 M) raw hMember.
have hLift f:k2 (lift f)=raw f.
  exact:(@LinearSubspaceLift.evaluation R DK DM E2
    (smooth_fixed_support_subspace hE2 M) k2 (smooth_fixed_test_space_laws hE2 M) raw hMember f).
have hLiftContinuous:open_family_continuous (smooth_test_step_opens hE1 hD1 K)
    (smooth_test_step_opens hE2 hD2 M) lift.
  apply:(@initial_open_topology_mapping DM E2 DK
    (smooth_function_opens hD2) k2 (smooth_test_step_opens hE2 hD2 M)
    (smooth_test_step_opens hE1 hD1 K) lift
    (smooth_test_step_relative_topology hE2 hD2 M)).2.
  have he:(fun f=>k2 (lift f))=(fun f=>raw f).
    apply:funext=>f;exact:hLift.
  rewrite he.
  exact:(@open_family_continuous_compose DK E1 E2
    (smooth_test_step_opens hE1 hD1 K) (smooth_function_opens hD1)
    (smooth_function_opens hD2) k1 P
    (initial_open_topology_inclusion (smooth_test_step_relative_topology hE1 hD1 K))
    hContinuous).
have hFactor:(fun f=>L (smooth_test_step hE1 K f))=
    (fun f=>smooth_test_step hE2 M (lift f)).
  apply:funext=>f;apply:(subspace_representation_injective (smooth_test_space_laws hE2)).
  by rewrite smooth_test_step_evaluation hLift hInclude smooth_test_step_evaluation.
rewrite hFactor.
exact:(@open_family_continuous_compose DK DM T2
  (smooth_test_step_opens hE1 hD1 K) (smooth_test_step_opens hE2 hD2 M)
  (smooth_test_opens hE2 hD2) lift (smooth_test_step hE2 M) hLiftContinuous
  (@final_open_topology_inclusion (smooth_compact_set hNX2 U2)
    (fun N=>smooth_fixed_test_space hE2 N) T2 (smooth_test_step_opens hE2 hD2)
    (fun N f=>smooth_test_step hE2 N f) (smooth_test_opens hE2 hD2)
    (smooth_test_final_topology_laws hE2 hD2) M)).
Qed.

(** Source for [smooth_test_operator_between_domains_continuous]:
    the original literal final topology makes a test
    operator continuous when its smooth extension is continuous
    and each compact support step has a common compact
    image support, supporting Federer 4.1.8, pp. 360–361.
    This requires no joint vector continuity of that topology. *)
Theorem smooth_test_operator_between_domains_continuous:
  (forall K:smooth_compact_set hNX1 U1,exists M:smooth_compact_set hNX2 U2,
    forall f:smooth_fixed_test_space hE1 K,
      @smooth_function_support R X2 Y2 NX2 hNX2 U2 E2 ev2
        (inc2 (L (smooth_test_step hE1 K f))) `<=` smooth_compact_carrier M)->
  open_family_continuous (smooth_test_opens hE1 hD1) (smooth_test_opens hE2 hD2) L.
Proof.
move=>hBound.
apply:(@final_open_topology_mapping (smooth_compact_set hNX1 U1)
  (fun K=>smooth_fixed_test_space hE1 K) T1 T2
  (smooth_test_step_opens hE1 hD1) (fun K f=>smooth_test_step hE1 K f)
  (smooth_test_opens hE1 hD1) (smooth_test_opens hE2 hD2)
  L (smooth_test_final_topology_laws hE1 hD1)).2=>K.
have[M hM]:=hBound K.
exact:(smooth_test_operator_between_fixed_steps hM).
Qed.
End SmoothTestOperatorBetweenDomains.
