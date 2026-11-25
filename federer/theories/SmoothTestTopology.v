(** Federer (1969), 4.1.1, pp. 344–345: construct the literal
    final topology on the actual test-function space and retain
    the E-relative topology on each fixed-support step. The
    construction does not claim joint vector continuity for D. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import Hom RealNormUP ContinuousMultilinearSealed OpenFamilyTopologyUP
  InitialOpenTopologyUP InitialOpenTopologySandwich FinalOpenTopologyUP FinalOpenTopologySealed
  DirectedSeminormFamilyUP DirectedSeminormTopologySealed SeminormFamilyRestriction
  SmoothCompactSet SmoothFunctionSpaceUP SmoothFunctionDerivativesUP SmoothFunctionSeminormFamily
  SmoothFunctionTopology SmoothTestSpaces.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

Section TestFunctionTopology.
Variable R:realType.
Variables X Y:lmodType R.
Variables (NX:X->R) (NY:Y->R).
Hypothesis hNX:is_real_norm NX.
Hypothesis hNY:is_real_norm NY.
Variable U:set X.
Variable E:lmodType R.
Variable ev:E->X->Y.
Hypothesis hE:is_smooth_function_space hNX hNY U ev.
Local Notation Z := (fun k=>@ContinuousMultilinear.space R k X Y NX NY hNX hNY).
Variable D:forall k,X->Hom E (Z k).
Hypothesis hD:@is_smooth_function_derivatives R X Y NX NY hNX hNY U E ev D.
Local Notation KIndex := (smooth_compact_set hNX U).
Local Notation I := (nat * KIndex)%type.
Local Notation DK := (smooth_fixed_test_space hE).
Local Notation DT := (smooth_test_space hE).
Local Notation k := (smooth_fixed_test_inclusion hE).
Local Notation inc := (smooth_test_inclusion hE).
Local Notation j := (smooth_test_step hE).
Local Notation nu := (smooth_function_derivative_seminorm hD).
Local Notation p := (fun i:I=>nu i.2 i.1).
Local Notation hp := (smooth_function_seminorms_directed (smooth_function_derivative_seminorm_laws hD)).
Local Notation EO := (smooth_function_opens hD).
Local Notation hEO := (smooth_function_topology_laws hD).
Local Notation hPK := (fun K=>@restricted_seminorm_family_directed R E (DK K) I p hp (k K)).

(** Source for [smooth_test_step_opens]: the E-relative topology
    on D_K(U,Y), Federer 4.1.1, p. 344, specified by the original
    derivative seminorms after inclusion. *)
Definition smooth_test_step_opens (K:KIndex):set (set (DK K)):=
  @DirectedSeminormTopology.opens R (DK K) I
    (fun i f=>p i (k K f)) (hPK K).
Arguments smooth_test_step_opens K : clear implicits.

(** Source for [smooth_test_step_topology_laws]: the restricted
    derivative-seminorm neighbourhood base on D_K(U,Y), supporting
    Federer 4.1.1, pp. 344–345. *)
Lemma smooth_test_step_topology_laws K:
  is_seminorm_family_topology (fun i f=>p i (k K f)) (smooth_test_step_opens K).
Proof. exact:DirectedSeminormTopology.laws. Qed.
Arguments smooth_test_step_topology_laws K : clear implicits.

(** Source for [smooth_test_step_relative_topology]: these are
    exactly the E-relative open sets on D_K(U,Y), Federer 4.1.1,
    p. 344, before constructing the final topology on D(U,Y). *)
Theorem smooth_test_step_relative_topology K:
  is_initial_open_topology EO (k K) (smooth_test_step_opens K).
Proof.
exact:(restricted_seminorm_topology_initial hp hEO (smooth_test_step_topology_laws K)).
Qed.
Arguments smooth_test_step_relative_topology K : clear implicits.

(** Source for [smooth_test_opens]: the literal final topology
    specified by Federer 4.1.1, p. 344. This remains distinct
    from the locally convex inductive topology. *)
Definition smooth_test_opens:set (set DT):=
  @FinalOpenTopology.opens KIndex (fun K=>DK K) DT smooth_test_step_opens
    (fun K f=>j K f) (fun K=>(smooth_test_step_topology_laws K).1).

(** Source for [smooth_test_final_topology_laws]: a subset of
    D is open exactly when its inverse image is E-relatively open
    on every D_K, Federer 4.1.1, p. 344. *)
Theorem smooth_test_final_topology_laws:
  is_final_open_topology smooth_test_step_opens (fun K f=>j K f) smooth_test_opens.
Proof. exact:FinalOpenTopology.laws. Qed.

(** Source for [smooth_test_inclusion_continuous]: the inclusion
    D(U,Y) into E(U,Y) is continuous, Federer 4.1.1, p. 344. *)
Theorem smooth_test_inclusion_continuous:
  open_family_continuous smooth_test_opens EO inc.
Proof.
apply:(@final_open_topology_mapping KIndex (fun K=>DK K) DT E
  smooth_test_step_opens (fun K f=>j K f) smooth_test_opens EO inc
  smooth_test_final_topology_laws).2=>K A hA.
have h:=initial_open_topology_inclusion (smooth_test_step_relative_topology K) hA.
have he:[set f:DK K|A (inc (j K f))]=[set f:DK K|A (k K f)].
  apply:funext=>f; by rewrite /= smooth_test_step_evaluation.
by rewrite he.
Qed.

(** Source for [smooth_test_same_relative_topology]: E and D
    induce the same topology on each D_K, Federer 4.1.1, p. 344.
    The argument uses the actual inclusion maps and the final
    topology; it assumes no vector continuity of that final topology. *)
Theorem smooth_test_same_relative_topology K:
  is_initial_open_topology smooth_test_opens (j K) (smooth_test_step_opens K).
Proof.
apply:(initial_open_topology_sandwich (smooth_test_step_relative_topology K)
  (final_open_topology_inclusion smooth_test_final_topology_laws K)
  smooth_test_inclusion_continuous).
exact:smooth_test_step_evaluation.
Qed.
End TestFunctionTopology.
Arguments smooth_test_step_opens {R X Y NX NY hNX hNY U E ev} hE {D} hD K.
Arguments smooth_test_step_topology_laws {R X Y NX NY hNX hNY U E ev} hE {D} hD K.
Arguments smooth_test_opens {R X Y NX NY hNX hNY U E ev} hE {D} hD.
Arguments smooth_test_final_topology_laws {R X Y NX NY hNX hNY U E ev} hE {D} hD.
