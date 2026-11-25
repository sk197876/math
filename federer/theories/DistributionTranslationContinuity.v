(** Federer (1969), 4.1.8, p. 360: a current applied to
    the first-variable slice depends continuously on the second
    variables. This supporting translation-orbit theorem retains
    the original final topology and the finite-order bound of
    4.1.1, p. 345. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals lra.
From Federer Require Import Hom RealNormUP NormDifferentialUP NormOpenDomainLaws
  LinearBasis ModuleQuotient ContinuousMultilinearSealed NormClassOneUP
  SmoothCompactSet SmoothFunctionSpaceUP SmoothFunctionSupport SmoothFunctionDerivativesUP
  SmoothTestSubspaces SmoothTestSpaces SmoothTestTopology SmoothFunctionTopology SmoothDerivativeSeminormUP
  SmoothGlobalTranslationSealed TestGlobalTranslation TestGlobalTranslationLaws
  TestTranslationCommonSupport SmoothTranslationSeminormContinuity DistributionSupportedBound
  ContinuousRealDual.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section DistributionTranslationContinuity.
Variable R:realType.
Variables X Y:lmodType R.
Variables (NX:X->R) (NY:Y->R).
Hypothesis hNX:is_real_norm NX.
Hypothesis hNY:is_real_norm NY.
Variable d:nat.
Variable b:'I_d->X.
Hypothesis hb:is_basis b.
Variable E:lmodType R.
Variable ev:E->X->Y.
Hypothesis hE:is_smooth_function_space hNX hNY (fun _=>True) ev.
Local Notation Z := (fun j=>@ContinuousMultilinear.space R j X Y NX NY hNX hNY).
Variable D:forall j,X->Hom E (Z j).
Hypothesis hD:@is_smooth_function_derivatives R X Y NX NY hNX hNY (fun _=>True) E ev D.
Local Notation hFull := (fun x (_:True)=>norm_full_domain_interior NX x).
Local Notation DT := (smooth_test_space hE).
Local Notation inc := (smooth_test_inclusion hE).
Local Notation SO := (smooth_test_opens hE hD).
Local Notation hSO := (smooth_test_final_topology_laws hE hD).1.
Local Notation DD := (@continuous_real_dual_space R DT SO hSO).
Local Notation eD := (@continuous_real_dual_evaluation R DT SO hSO).
Local Notation L := (@SmoothGlobalTranslation.operator R X Y NX NY hNX hNY E ev hE).
Local Notation hL := (@SmoothGlobalTranslation.laws R X Y NX NY hNX hNY E ev hE).
Local Notation A := (fun c=>@test_global_translation R X Y NX NY hNX hNY E ev hE c (L c) (hL c)).

(** Source for [distribution_translation_orbit_continuous]: applying
    an arbitrary continuous distribution to an actual translated
    test gives a continuous scalar function. This supports the
    smooth slice in Federer 4.1.8, p. 360, without an integral
    representation premise on the distribution. *)
Theorem distribution_translation_orbit_continuous (T:DD) (f:DT):
  norm_class_zero NX (fun t:R^o=>`|t|) (fun _=>True)
    (fun c=>eD T (A c f)).
Proof.
move=>c _; split; first exact:norm_full_domain_interior NX c.
move=>eta hEta.
have[C hCommon]:=@test_translation_common_support R X Y NX NY hNX hNY
  d b hb E ev hE (A c f).
have hBase:@smooth_function_support R X Y NX hNX (fun _=>True) E ev
    (inc (A c f)) `<=` smooth_compact_carrier C.
  have hZero:NX 0<=1 by rewrite (real_seminorm_zero hNX.1); exact:ler01.
  have h:=hCommon 0 hZero.
  by rewrite (@test_global_translation_zero R X Y NX NY hNX hNY E ev hE) in h.
have hT:=@continuous_real_dual_member_continuous R DT SO hSO T.
have[i [M hBound]]:=@distribution_supported_local_bound R X Y NX NY hNX hNY
  (fun _=>True) hFull E ev hE D hD (eD T) hT C.
have hM:(0<=(M%:R:R)):=ler0n R M.
have hDen:0<(M%:R:R)+1 by lra.
have hSmall:0<eta/(M%:R+1) by rewrite divr_gt0.
have[r [hr hEstimate]]:=@smooth_translation_seminorm_continuity R X Y NX NY hNX hNY
  E ev D hD L hL (inc (A c f)) C i (eta/(M%:R+1)) hSmall.
exists (Num.min 1 r); split; first by rewrite lt_min ltr01 hr.
move=>h _; rewrite lt_min=>/andP [hh1 hhr].
pose g:=A h (A c f)-A c f.
have hSupport:@smooth_function_support R X Y NX hNX (fun _=>True) E ev
    (inc g) `<=` smooth_compact_carrier C.
  change (smooth_fixed_support_subspace hE C (inc g)).
  rewrite /g linearB /=.
  exact:(@subspace_sub R E (smooth_fixed_support_subspace hE C)
    (inc (A h (A c f))) (inc (A c f)) (hCommon h (ltW hh1)) hBase).
have hPair:eD T g=eD T (A (c+h) f)-eD T (A c f).
  by rewrite /g linearB /=
    (@test_global_translation_composition R X Y NX NY hNX hNY E ev hE) (addrC h c).
have hInc:inc g=L h (inc (A c f))-inc (A c f).
  by rewrite /g linearB /=
    (@test_global_translation_inclusion R X Y NX NY hNX hNY E ev hE h (L h) (hL h)).
have hFinite:=hBound g hSupport.
rewrite hPair hInc in hFinite.
have hNu:=hEstimate h hhr.
have hNonnegative:=smooth_derivative_seminorm_nonnegative
  (smooth_function_derivative_seminorm_laws hD C i)
    (L h (inc (A c f))-inc (A c f)).
have hStrict:(M%:R+1)*smooth_function_derivative_seminorm hD C i
    (L h (inc (A c f))-inc (A c f))<(M%:R+1)*(eta/(M%:R+1)).
  by rewrite ltr_pM2l.
have hEq:(M%:R+1)*(eta/(M%:R+1))=eta by rewrite mulrC divfK // gt_eqF.
rewrite hEq in hStrict.
apply:le_lt_trans hFinite _; nra.
Qed.
End DistributionTranslationContinuity.
