(** Federer (1969), 4.1.14, p. 371: the local
    cutoff formula defines an original current once,
    on every compact family of target tests, it agrees
    with one already defined current. The literal final
    test topology of 4.1.1, pp. 344–345, supplies
    continuity. No joint vector continuity of that
    topology is assumed or asserted. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  AlternatingForms CurrentCoefficientNorms CurrentSpaces CurrentSupportGeometry CurrentEvaluation SmoothCompactSet
  SmoothFunctionSupport SmoothTestSpaces SmoothTestEvaluation SmoothTestTopology
  SmoothTestSubspaces LinearSubspaceRepresentationUP ContinuousRealDual
  NormOpenTopology OpenFamilyTopologyUP FinalOpenTopologyUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section CurrentLocalTestAction.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n m:nat.
Local Notation X:=(R_n R n).
Local Notation NX:=(inner_norm (@euclidean_inner_productP R n)).
Local Notation hNX:=(inner_norm_real_norm (@euclidean_inner_productP R n)).
Variable U:set X.
Hypothesis hU:forall x,U x->norm_domain_interior NX U x.
Local Notation DT:=(@current_test_space R h2 n U hU m).
Local Notation C:=(@current_space R h2 n U hU m).
Local Notation action:=(@current_value R h2 n U hU m).
Local Notation support:=(@current_test_support R h2 n m U hU).
Local Notation hE:=(@current_smooth_space_laws R h2 n U hU m).
Local Notation hD:=(@current_smooth_derivative_laws R h2 n U hU m).
Local Notation O:=(@current_test_opens R h2 n U hU m).
Local Notation OR:=(norm_open_family (@scalar_absolute_value_norm R)).
Local Notation Step:=(smooth_test_step hE).
Variable L:DT->R^o.

(** Source for [is_current_local_test_action]: on every
    original compact target support the proposed local
    action agrees with an actual current, supporting
    the definition in Federer 4.1.14, p. 371.
    This property is independent of any selected
    current or chosen cutoff construction. *)
Definition is_current_local_test_action:Prop:=
  forall K:smooth_compact_set hNX U,exists S:C,
    forall phi:DT,support phi `<=` smooth_compact_carrier K->L phi=action S phi.
Hypothesis hLocal:is_current_local_test_action.

(** Source for [current_local_test_action_linear]: one
    common compact test bound proves linearity of the
    original local action, supporting Federer 4.1.14,
    p. 371. No regularity of a nonsmooth pullback
    is required in this local construction. *)
Theorem current_local_test_action_linear:linear L.
Proof.
move=>c phi psi.
have[K hK]:=smooth_test_support_bound hE phi.
have[J hJ]:=smooth_test_support_bound hE psi.
have[B hB]:=smooth_test_support_bound hE (c*:phi+psi).
pose A:=smooth_compact_union (smooth_compact_union K J) B.
have hPhi:support phi `<=` smooth_compact_carrier A.
  move=>x hx;left;left;exact:hK x hx.
have hPsi:support psi `<=` smooth_compact_carrier A.
  move=>x hx;left;right;exact:hJ x hx.
have hCombination:support (c*:phi+psi) `<=` smooth_compact_carrier A.
  move=>x hx;right;exact:hB x hx.
have[S hS]:=hLocal A.
rewrite (hS _ hCombination) (hS _ hPhi) (hS _ hPsi).
exact:linearP.
Qed.

(** Source for [current_test_step_support_bound]: every
    test in the original fixed-support step D_K has
    its actual support in K, by 4.1.1, p. 344,
    supporting the local construction in 4.1.14, p. 371. *)
Lemma current_test_step_support_bound (K:smooth_compact_set hNX U)
    (a:smooth_fixed_test_space hE K):
  support (Step K a) `<=` smooth_compact_carrier K.
Proof.
change (@smooth_function_support R X (A_m X R^o m) NX hNX
  U (@current_smooth_space R h2 n U hU m) (@current_smooth_value R h2 n U hU m)
  (smooth_test_inclusion hE (Step K a)) `<=` smooth_compact_carrier K).
rewrite smooth_test_step_evaluation.
exact:subspace_representation_member (smooth_fixed_test_space_laws hE K) a.
Qed.

(** Source for [current_local_test_action_continuous]: the
    exact final-topology mapping law proves continuity
    of the original local action, supporting Federer
    4.1.14, p. 371, by 4.1.1, pp. 344–345. *)
Theorem current_local_test_action_continuous:open_family_continuous O OR L.
Proof.
apply:(@final_open_topology_mapping (smooth_compact_set hNX U)
  (fun K=>smooth_fixed_test_space hE K) DT R^o
  (smooth_test_step_opens hE hD) (fun K a=>Step K a) O OR L
  (smooth_test_final_topology_laws hE hD)).2=>K.
have[S hS]:=hLocal K.
have hStep:=final_open_topology_inclusion (smooth_test_final_topology_laws hE hD) K.
have hAction:open_family_continuous O OR (action S).
  exact:(@continuous_real_dual_member_continuous R DT O
    (smooth_test_final_topology_laws hE hD).1 S).
have hComposite:=open_family_continuous_compose hStep hAction.
have hFunctions:(fun a:smooth_fixed_test_space hE K=>L (Step K a))=
    (fun a:smooth_fixed_test_space hE K=>action S (Step K a)).
  apply:funext=>a;exact:(hS _ (@current_test_step_support_bound K a)).
rewrite -hFunctions in hComposite.
exact:hComposite.
Qed.

(** Source for [current_local_test_action_exists]: the
    proposed local action is represented by an actual
    original current, supporting Federer 4.1.14,
    p. 371. Existence uses the already proved
    opaque continuous-dual representation. *)
Theorem current_local_test_action_exists:
  exists Q:C,forall phi:DT,action Q phi=L phi.
Proof.
pose F:Hom DT R^o:=@HomMap R DT R^o L
  (introT (asboolP _) current_local_test_action_linear).
have hContinuous:open_family_continuous O OR F:=current_local_test_action_continuous.
have[Q hQ]:=@continuous_real_dual_represents R DT O
  (smooth_test_final_topology_laws hE hD).1 F hContinuous.
exists Q=>phi;exact:(congr1 (fun H:Hom DT R^o=>H phi) hQ).
Qed.
End CurrentLocalTestAction.
