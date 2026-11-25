(** Federer (1969), 4.1.7, p. 359:
    properness on the original current
    support gives a unique actual current
    f#T. Compact cutoff replacements prove
    its action, linearity and continuity
    on each fixed-support step of
    Federer's literal final test topology. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP NormRegularity InnerNorm
  HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct AlternatingForms
  CurrentCoefficientNorms CurrentSpaces CurrentEvaluation CurrentProperSupport CurrentProperPullbackTests
  CurrentPushforwardUP SmoothCompactSet SmoothFormPullbackSealed SmoothFunctionSupport
  SmoothTestSubspaces SmoothTestSpaces SmoothTestEvaluation SmoothTestTopology SmoothFunctionTopology
  LinearSubspaceRepresentationUP FinalOpenTopologyUP InitialOpenTopologyUP
  OpenFamilyTopologyUP NormOpenTopology ContinuousRealDual.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section CurrentPushforwardExistence.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables v n m:nat.
Local Notation X := (R_n R v).
Local Notation Y := (R_n R n).
Local Notation NX := (inner_norm (@euclidean_inner_productP R v)).
Local Notation NY := (inner_norm (@euclidean_inner_productP R n)).
Local Notation hNX := (inner_norm_real_norm (@euclidean_inner_productP R v)).
Local Notation hNY := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation B := (A_m Y R^o m).
Variables (U:X->Prop) (V:Y->Prop).
Hypothesis hU:forall x,U x->norm_domain_interior NX U x.
Arguments hU : clear implicits.
Hypothesis hV:forall y,V y->norm_domain_interior NY V y.
Arguments hV : clear implicits.
Local Notation CT := (@current_space R h2 v U hU m).
Local Notation CS := (@current_space R h2 n V hV m).
Local Notation DU := (@current_test_space R h2 v U hU m).
Local Notation DV := (@current_test_space R h2 n V hV m).
Local Notation hE := (@current_smooth_space_laws R h2 n V hV m).
Local Notation hF := (@current_smooth_space_laws R h2 v U hU m).
Local Notation E := (@current_smooth_space R h2 n V hV m).
Local Notation ev := (@current_smooth_value R h2 n V hV m).
Local Notation DE := (@current_smooth_derivatives R h2 n V hV m).
Local Notation hDE := (@current_smooth_derivative_laws R h2 n V hV m).
Local Notation hDF := (@current_smooth_derivative_laws R h2 v U hU m).
Local Notation OE := (smooth_function_opens hDE).
Local Notation OU := (@current_test_opens R h2 v U hU m).
Local Notation OV := (@current_test_opens R h2 n V hV m).
Local Notation OR := (norm_open_family (@scalar_absolute_value_norm R)).
Variable T:CT.
Variable f:X->Y.
Hypothesis hImage:forall x,U x->V (f x).
Arguments hImage : clear implicits.
Hypothesis hf:norm_class_all_orders hNX hNY U f.
Hypothesis hProper:@is_current_proper_on_support R h2 v n m U hU V T f hImage.
Local Notation agree := (@is_current_pullback_test_replacement R h2 v n m U V hU hV T f hImage hf).
Local Notation pushlaw := (@is_current_pushforward R h2 v n m U V hU hV T f hImage hf).
Local Notation action := (@current_value R h2 v U hU m T).

(** Source for [current_pushforward_test_replacement_exists]:
    every actual target test has
    a compact source replacement of
    its original pullback near spt T,
    supporting Federer 4.1.7, p. 359.
    The printed properness hypothesis supplies
    the compact inverse-image locus. *)
Lemma current_pushforward_test_replacement_exists (phi:DV):exists psi:DU,agree phi psi.
Proof.
have [K hK]:=smooth_test_support_bound hE phi.
have [Q [hQC [W [hW [hTW [hWU hAgreement]]]]]]:=
  @current_proper_pullback_tests R h2 v n m m U V hU hV T f hImage hf hProper K.
exists (Q (smooth_test_inclusion hE phi)),W;split=>//;split=>//;split=>//.
exact:(hAgreement (smooth_test_inclusion hE phi) hK).
Qed.

(** Source for [current_pushforward_private_value]:
    private choice of a proved
    compact replacement, used only inside
    the existence proof of f#T
    in Federer 4.1.7, p. 359. *)
Definition current_pushforward_private_value (phi:DV):R^o:=
  action (projT1 (cid (current_pushforward_test_replacement_exists phi))).

(** Source for [current_pushforward_private_action]:
    every valid compact replacement has
    the same original defining value,
    supporting Federer 4.1.7, p. 359. *)
Lemma current_pushforward_private_action phi psi:
  agree phi psi->current_pushforward_private_value phi=action psi.
Proof.
move=>hPsi;exact:(@current_pullback_test_value_unique R h2 v n m U V hU hV T f hImage hf
  phi _ psi (projT2 (cid (current_pushforward_test_replacement_exists phi))) hPsi).
Qed.

(** Source for [current_pushforward_private_linear]:
    the defining value is linear
    on the original target tests,
    supporting Federer 4.1.7, p. 359.
    A common open support neighbourhood
    compares the independently chosen replacements. *)
Lemma current_pushforward_private_linear:linear current_pushforward_private_value.
Proof.
move=>c phi eta.
pose psi:=projT1 (cid (current_pushforward_test_replacement_exists phi)).
pose chi:=projT1 (cid (current_pushforward_test_replacement_exists eta)).
have hPsi:=projT2 (cid (current_pushforward_test_replacement_exists phi)).
have hChi:=projT2 (cid (current_pushforward_test_replacement_exists eta)).
have hCombination:=@current_pullback_test_replacement_linear R h2 v n m U V hU hV T f hImage hf
  c phi eta psi chi hPsi hChi.
rewrite (current_pushforward_private_action hCombination).
exact:(linearP action c psi chi).
Qed.

(** Source for [current_pushforward_private_continuous]:
    fixed compact target supports have
    continuous cutoff pullback actions. The
    original final topology then gives
    continuity on all actual tests,
    supporting Federer 4.1.7, p. 359.
    No joint vector continuity of
    that topology is asserted. *)
Lemma current_pushforward_private_continuous:
  open_family_continuous OV OR current_pushforward_private_value.
Proof.
apply:(@final_open_topology_mapping (smooth_compact_set hNY V)
  (fun K=>smooth_fixed_test_space hE K) DV R^o
  (smooth_test_step_opens hE hDE) (fun K a=>smooth_test_step hE K a)
  OV OR current_pushforward_private_value (smooth_test_final_topology_laws hE hDE)).2=>K.
have [Q [hQC [W [hW [hTW [hWU hAgreement]]]]]]:=
  @current_proper_pullback_tests R h2 v n m m U V hU hV T f hImage hf hProper K.
have hActionC:open_family_continuous OU OR action.
  exact:(@continuous_real_dual_member_continuous R DU OU
    (smooth_test_final_topology_laws hF hDF).1 T).
have hInc:open_family_continuous (smooth_test_step_opens hE hDE K) OE
    (smooth_fixed_test_inclusion hE K).
  exact:(initial_open_topology_inclusion (smooth_test_step_relative_topology hE hDE K)).
have hComposite:=open_family_continuous_compose hInc (open_family_continuous_compose hQC hActionC).
have hValue a:current_pushforward_private_value (smooth_test_step hE K a)=
    action (Q (smooth_fixed_test_inclusion hE K a)).
  have hFixed:@smooth_function_support R Y B NY hNY V E ev
      (smooth_fixed_test_inclusion hE K a) `<=` smooth_compact_carrier K.
    exact:(subspace_representation_member (smooth_fixed_test_space_laws hE K) a).
  apply:current_pushforward_private_action.
  exists W;split=>//;split=>//;split=>// x hx.
  change (@current_test_value R h2 v U hU m (Q (smooth_fixed_test_inclusion hE K a)) x=
    @current_smooth_value R h2 v U hU m
      (@SmoothFormPullback.operator R h2 v n m U V hU hV f hImage hf
        (smooth_test_inclusion hE (smooth_test_step hE K a))) x).
  rewrite smooth_test_step_evaluation;exact:hAgreement _ hFixed x hx.
move=>A hA.
have hOpen:=hComposite A hA.
have hEqual:[set a|A (current_pushforward_private_value (smooth_test_step hE K a))]=
    [set a|A (action (Q (smooth_fixed_test_inclusion hE K a)))].
  apply:funext=>a;exact:(congr1 A (hValue a)).
by rewrite hEqual.
Qed.

(** Source for [current_pushforward_exists]:
    the original proper pushforward is
    an actual current with the
    independent compact-replacement action law,
    Federer 4.1.7, p. 359. *)
Theorem current_pushforward_exists:exists S:CS,pushlaw S.
Proof.
pose L:Hom DV R^o:=@HomMap R DV R^o current_pushforward_private_value
  (introT (asboolP _) current_pushforward_private_linear).
have [S hS]:=@continuous_real_dual_represents R DV OV
  (smooth_test_final_topology_laws hE hDE).1 L current_pushforward_private_continuous.
exists S=>phi psi hPsi.
change (@continuous_real_dual_evaluation R DV OV
  (smooth_test_final_topology_laws hE hDE).1 S phi=action psi).
rewrite hS;exact:current_pushforward_private_action hPsi.
Qed.

(** Source for [current_pushforward_unique]:
    the original defining action determines
    a unique current, supporting Federer
    4.1.7, p. 359. Replacement
    existence is proved from properness. *)
Theorem current_pushforward_unique (S Z:CS):pushlaw S->pushlaw Z->S=Z.
Proof.
move=>hS hZ;apply:(@current_values_extensional R h2 n m V hV)=>phi.
have [psi hPsi]:=current_pushforward_test_replacement_exists phi.
by rewrite (hS phi psi hPsi) (hZ phi psi hPsi).
Qed.
End CurrentPushforwardExistence.
