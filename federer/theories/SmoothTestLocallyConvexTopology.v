(** Federer (1969), 4.1.1, pp. 344–345;
    Menne (2016), Definition 2.13 and Remarks 2.14–2.17,
    p. 996: compare the two actual topologies on the
    original test space without identifying them. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import Hom RealNormUP ContinuousMultilinearSealed OpenFamilyTopologyUP
  DirectedSeminormFamilyUP SeminormFamilyRestriction InductiveLimitSeminormFamilyUP InductiveLimitTopology
  InductiveLimitTopologyMapping NormOpenTopology SmoothCompactSet SmoothFunctionSpaceUP SmoothFunctionDerivativesUP
  SmoothFunctionSeminormFamily SmoothFunctionTopology SmoothTestSpaces SmoothTestTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Section TestLocallyConvexTopology.
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


Local Notation pK := (fun (K:KIndex) (i:I) (f:DK K)=>p i (k K f)).
Local Notation SO := (smooth_test_opens hE hD).

(** Source for [smooth_test_locally_convex_opens]: the
    actual locally convex inductive topology of
    Menne (2016), Definition 2.13, p. 996,
    on Federer's D(U,Y), 4.1.1, p. 344. *)
Definition smooth_test_locally_convex_opens:set (set DT):=
  @inductive_limit_opens R DT KIndex DK (fun _=>I) pK j hPK.

(** Source for [smooth_test_locally_convex_laws]: the
    actual comparison topology has exactly the independent
    compatible-seminorm laws, Menne (2016), Definition 2.13,
    p. 996, qualifying Federer 4.1.1, p. 344. *)
Theorem smooth_test_locally_convex_laws:
  is_inductive_limit_open_topology pK j smooth_test_locally_convex_opens.
Proof. exact:inductive_limit_opens_laws. Qed.

(** Source for [smooth_test_final_finer_locally_convex]: the
    actual locally convex topology is coarser than
    Federer's literal final topology, 4.1.1, p. 344;
    Menne (2016), Remark 2.17, p. 996. *)
Theorem smooth_test_final_finer_locally_convex A:
  smooth_test_locally_convex_opens A ->SO A.
Proof.
exact:(@final_topology_finer_than_inductive R DT KIndex DK (fun _=>I) pK j
  (smooth_test_step_opens hE hD) hPK (smooth_test_step_topology_laws hE hD)
  smooth_test_locally_convex_opens smooth_test_locally_convex_laws SO
  (smooth_test_final_topology_laws hE hD) A).
Qed.

(** Source for [smooth_test_locally_convex_linear_continuity]:
    both actual test topologies have the same
    continuous linear maps into any seminorm-defined
    locally convex space, Menne (2016), Remark 2.17,
    p. 996; this preserves Federer's distribution
    dual in 4.1.1, p. 345. *)
Theorem smooth_test_locally_convex_linear_continuity (F:lmodType R) (A:Type)
    (r:A->F->R) (O:set (set F))
    (hr:is_directed_seminorm_family r) (hO:is_seminorm_family_topology r O) (L:Hom DT F):
  open_family_continuous SO O L <->
  open_family_continuous smooth_test_locally_convex_opens O L.
Proof.
exact:(@final_inductive_linear_continuity_iff R DT KIndex DK (fun _=>I) pK j
  (smooth_test_step_opens hE hD) hPK (smooth_test_step_topology_laws hE hD)
  smooth_test_locally_convex_opens smooth_test_locally_convex_laws SO F A r O hr hO L
  (smooth_test_final_topology_laws hE hD)).
Qed.

(** Source for [smooth_test_same_continuous_real_dual]: the
    actual two test topologies define exactly the
    same distributions, Menne (2016), Remark 2.17,
    p. 996, with Federer's definition in
    4.1.1, p. 345. *)
Theorem smooth_test_same_continuous_real_dual (L:Hom DT R^o):
  open_family_continuous SO (norm_open_family (@scalar_absolute_value_norm R)) L <->
  open_family_continuous smooth_test_locally_convex_opens (norm_open_family (@scalar_absolute_value_norm R)) L.
Proof.
exact:(smooth_test_locally_convex_linear_continuity (norm_single_seminorm_directed (@scalar_absolute_value_norm R))
  (norm_open_family_seminorm_laws (@scalar_absolute_value_norm R)) L).
Qed.
End TestLocallyConvexTopology.
