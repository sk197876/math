(** Federer (1969), 4.1.1, p. 345: every compactly
    supported distribution extends to a continuous real
    functional on E(U,Y). The witness is composition
    with the proved compact cutoff replacement; its
    agreement and exact support are proved independently. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets reals.
From Federer Require Import Hom RealNormUP NormDifferentialUP LinearBasis ContinuousMultilinearSealed
  OpenFamilyTopologyUP NormOpenTopology SmoothCompactSet SmoothFunctionSpaceUP
  SmoothFunctionDerivativesUP SmoothFunctionTopology SmoothFunctionSupport SmoothTestSpaces
  SmoothTestEvaluation SmoothTestTopology SmoothCutoffReplacement SmoothLocalAgreementSeminorm
  FunctionalSupportUP SmoothTestFunctionalSupport SmoothDualSupportTransport.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section CompactDistributionExtension.
Variable R:realType.
Variables X Y:lmodType R.
Variables (NX:X->R) (NY:Y->R).
Hypothesis hNX:is_real_norm NX.
Hypothesis hNY:is_real_norm NY.
Variable n:nat.
Variable b:'I_n->X.
Hypothesis hb:is_basis b.
Variable U:set X.
Hypothesis hU:forall x,U x ->norm_domain_interior NX U x.
Variable E:lmodType R.
Variable ev:E->X->Y.
Hypothesis hE:is_smooth_function_space hNX hNY U ev.
Local Notation Z := (fun k=>@ContinuousMultilinear.space R k X Y NX NY hNX hNY).
Variable D:forall k,X->Hom E (Z k).
Hypothesis hD:@is_smooth_function_derivatives R X Y NX NY hNX hNY U E ev D.
Local Notation EO := (smooth_function_opens hD).
Local Notation DT := (smooth_test_space hE).
Local Notation inc := (smooth_test_inclusion hE).
Local Notation value := (smooth_test_value hE).
Local Notation SO := (smooth_test_opens hE hD).
Local Notation RO := (norm_open_family (@scalar_absolute_value_norm R)).
Local Notation support := (@smooth_function_support R X Y NX hNX U DT value).
Local Notation tsupport := (@smooth_functional_support R X Y NX hNX U DT value).
Variable K:smooth_compact_set hNX U.
Local Notation C := (@smooth_cutoff_replacement R X Y NX NY hNX hNY n b hb U hU E ev hE K).

(** Source for [compact_distribution_extension_exists]: an
    actual E-continuous functional extends the given
    distribution and retains its compact support bound,
    the surjectivity onto compact-support distributions
    in Federer 4.1.1, p. 345. *)
Theorem compact_distribution_extension_exists (T:Hom DT R^o):
  open_family_continuous SO RO T ->
  tsupport T `<=` smooth_compact_carrier K ->
  exists L:Hom E R^o,open_family_continuous EO RO L /\
    (forall f:DT,L (inc f)=T f) /\
    @smooth_functional_support R X Y NX hNX U E ev L `<=` smooth_compact_carrier K.
Proof.
move=>hT hK.
pose L:=hom_comp T C.
have hL:open_family_continuous EO RO L.
  exact:(@open_family_continuous_compose E DT R^o EO SO RO C T
    (@smooth_cutoff_replacement_continuous R X Y NX NY hNX hNY n b hb U hU E ev hE D hD K) hT).
have [W [hW [hKW [hWU hAgree]]]]:=
  @smooth_cutoff_replacement_agrees_near_compact R X Y NX NY hNX hNY n b hb U hU E ev hE K.
have hRestr (f:DT):L (inc f)=T f.
  pose d:=C (inc f)-f.
  have hZero x (hx:W x):value d x=0.
    have hVal:value d x=value (C (inc f)) x-value f x:=
      congr1 (fun q:X->Y=>q x) (linearB (smooth_test_values_hom hE) (C (inc f)) f).
    rewrite hVal.
    change (ev (inc (C (inc f))) x-ev (inc f) x=0).
    by rewrite (hAgree (inc f) x hx) subrr.
  have hd:T d=0.
    apply:(@smooth_test_functional_disjoint_support_zero R X Y NX NY hNX hNY n b hb U hU E ev hE T d)=>x ht hp.
    exact:(@smooth_support_avoids_open_zero_set R X Y NX hNX U DT value d W hW hZero
      x (hKW x (hK x ht)) hp).
  rewrite /d linearB in hd.
  change (T (C (inc f))=T f).
  by apply/eqP; rewrite -subr_eq0 hd eqxx.
have hHom:hom_comp L inc=T.
  apply:hom_ext=>f; rewrite hom_compE; exact:hRestr.
have hSupport:=@smooth_dual_support_restriction R X Y NX NY hNX hNY n b hb U hU E ev hE D hD L hL.
exists L; split=>//; split; first exact hRestr.
by rewrite hSupport hHom.
Qed.
End CompactDistributionExtension.
