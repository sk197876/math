(** Federer (1969), 4.1.2, p. 347: translated
    smooth kernels depend continuously on the centre in
    every original finite derivative seminorm. Compact-nearby
    uniform continuity supplies one radius for all base points. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals lra.
From Federer Require Import Hom RealNormUP NormMetric ContinuousMultilinearSealed ContinuousMultilinearNorm
  CompactNearbyUniformContinuity SmoothCompactSet SmoothFunctionSpaceUP SmoothFunctionDerivativesUP
  SmoothDerivativeSeminormUP SmoothFunctionTopology SmoothGlobalTranslationUP SmoothGlobalTranslationDerivatives.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Section SmoothTranslationSeminormContinuity.
Variable R:realType.
Variables X Y:lmodType R.
Variables (NX:X->R) (NY:Y->R).
Hypothesis hNX:is_real_norm NX.
Hypothesis hNY:is_real_norm NY.
Variable E:lmodType R.
Variable ev:E->X->Y.
Local Notation Z := (fun j=>@ContinuousMultilinear.space R j X Y NX NY hNX hNY).
Local Notation ZN := (fun j=>@ContinuousMultilinear.norm R j X Y NX NY hNX hNY).
Variable D:forall j,X->Hom E (Z j).
Hypothesis hD:@is_smooth_function_derivatives R X Y NX NY hNX hNY (fun _=>True) E ev D.
Variable L:X->Hom E E.
Hypothesis hL:forall c,is_smooth_global_translation ev c (L c).

(** Source for [smooth_translation_seminorm_continuity]: all
    derivatives of a translated kernel vary uniformly
    on the compact used by the distribution bound
    in Federer 4.1.2, p. 347. *)
Theorem smooth_translation_seminorm_continuity f
    (K:smooth_compact_set hNX (fun _=>True)) i eta:
  0<eta ->exists d:R,0<d /\ forall c,NX c<d ->
    smooth_function_derivative_seminorm hD K i (L c f-f)<eta.
Proof.
move=>hEta; have hHalf:0<eta/2 by rewrite divr_gt0 // ltr0n.
have hJet j:exists d:R,0<d /\ forall c,NX c<d ->forall x,
    smooth_compact_carrier K x ->@ZN j (@D j x (L c f-f))<eta/2.
  pose hNj:=continuous_multilinear_norm_is_norm hNY
    (@ContinuousMultilinear.laws R j X Y NX NY hNX hNY).
  have[d [hd hb]]:=@norm_class_zero_compact_uniform_nearby R X (Z j) NX (@ZN j) hNX hNj
    (fun _=>True) (smooth_compact_carrier K) (fun x=>@D j x f)
    (smooth_compact_is_compact K) (fun _ _=>Logic.I)
    (@smooth_derivative_continuous R X Y NX NY hNX hNY (fun _=>True) E ev D hD j f)
    (eta/2) hHalf.
  exists d; split=>// c hc x hx.
  have hValue:@D j x (L c f-f)=@D j (x+c) f-@D j x f.
    rewrite linearB /=.
    by rewrite (@smooth_global_translation_derivatives R X Y NX NY hNX hNY E ev D hD c (L c) (hL c)).
  rewrite hValue; apply:(hb x (x+c) hx Logic.I).
  by rewrite (addrC x c) addrK.
have hFinite m:exists d:R,0<d /\ forall c,NX c<d ->forall j,(j<=m)%N ->
    forall x,smooth_compact_carrier K x ->@ZN j (@D j x (L c f-f))<eta/2.
  elim:m=>[|m [d [hd hb]]].
  - have[d [hd hb]]:=hJet 0%N.
    exists d; split=>// c hc j; rewrite leqn0=>/eqP ->; exact:hb c hc.
  - have[s [hs hNext]]:=hJet m.+1.
    exists (Num.min d s); split; first by rewrite lt_min hd hs.
    move=>c hc j hj.
    have hMinL:Num.min d s<=d by rewrite ge_min lexx.
    have hMinR:Num.min d s<=s by rewrite ge_min lexx orbT.
    have hcd:NX c<d:=lt_le_trans hc hMinL.
    have hcs:NX c<s:=lt_le_trans hc hMinR.
    case:(eqVneq j m.+1)=>[->|hNe]; first exact:hNext c hcs.
    have hjm:(j<=m)%N by move:hj; rewrite leq_eqVlt (negPf hNe) /= ltnS.
    exact:hb c hcd j hjm.
have[d [hd hb]]:=hFinite i.
exists d; split=>// c hc.
have hBound:smooth_function_derivative_seminorm hD K i (L c f-f)<=eta/2.
  apply:(@smooth_derivative_seminorm_least R X Y NX NY hNX hNY (fun _=>True) E D K i
    (smooth_function_derivative_seminorm hD K i) (smooth_function_derivative_seminorm_laws hD K i)
    (L c f-f) (eta/2) (ltW hHalf)).
  move=>j hj x hx; exact:ltW (hb c hc j hj x hx).
apply:le_lt_trans hBound _; lra.
Qed.
End SmoothTranslationSeminormContinuity.
