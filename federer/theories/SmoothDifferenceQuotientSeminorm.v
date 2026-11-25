(** Federer (1969), 4.1.1, p. 346: the
    original finite derivative seminorms of the
    Taylor quotient error tend to zero. Finitely
    many compact-uniform derivative estimates give
    one common positive increment radius. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals lra.
From Federer Require Import Hom RealNormUP NormDifferentialUP ContinuousMultilinearSealed
  SmoothCompactSet SmoothFunctionSpaceUP SmoothFunctionDerivativesUP SmoothDerivativeSeminormUP
  SmoothFunctionTopology SmoothDirectionalDerivativeUP SmoothGlobalTranslationUP SmoothDifferenceQuotientJets.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Section DifferenceQuotientSeminorm.
Variable R:realType.
Variables X Y:lmodType R.
Variables (NX:X->R) (NY:Y->R).
Hypothesis hNX:is_real_norm NX.
Hypothesis hNY:is_real_norm NY.
Variable E:lmodType R.
Variable ev:E->X->Y.
Hypothesis hE:is_smooth_function_space hNX hNY (fun _=>True) ev.
Local Notation Z := (fun k=>@ContinuousMultilinear.space R k X Y NX NY hNX hNY).
Local Notation ZN := (fun k=>@ContinuousMultilinear.norm R k X Y NX NY hNX hNY).
Variable D:forall k,X->Hom E (Z k).
Hypothesis hD:@is_smooth_function_derivatives R X Y NX NY hNX hNY (fun _=>True) E ev D.
Variable v:X.
Variable P:Hom E E.
Hypothesis hP:@is_smooth_directional_derivative R X Y NX NY hNX hNY (fun _=>True) E ev D v P.
Variable L:X->Hom E E.
Hypothesis hL:forall c,is_smooth_global_translation ev c (L c).
Local Notation err := (@smooth_difference_quotient_error R X E v P L).

(** Source for [smooth_difference_quotient_seminorm_limit]:
    each nu^i_K of the actual quotient error
    tends to zero, supporting the D-convergence
    asserted in Federer 4.1.1, p. 346. *)
Theorem smooth_difference_quotient_seminorm_limit f (K:smooth_compact_set hNX (fun _=>True)) i:
  forall e:R,0<e ->exists d:R,0<d /\ forall t,0<`|t|<d ->
    smooth_function_derivative_seminorm hD K i (err t f)<e.
Proof.
move=>e he; have hr:0<e/2 by rewrite divr_gt0 // ltr0n.
have hFinite m:exists d:R,0<d /\ forall t,0<`|t|<d ->forall j,(j<=m)%N ->
    forall x,smooth_compact_carrier K x ->@ZN j (@D j x (err t f))<e/2.
  elim:m=>[|m [d [hd hb]]].
  - have [d [hd hb]]:=@smooth_difference_quotient_jet R X Y NX NY hNX hNY E ev hE D hD
      v P hP L hL 0%N f K (e/2) hr.
    exists d; split=>// t ht j; rewrite leqn0=>/eqP ->; exact:hb t ht.
  - have [s [hs hNext]]:=@smooth_difference_quotient_jet R X Y NX NY hNX hNY E ev hE D hD
      v P hP L hL m.+1 f K (e/2) hr.
    exists (Num.min d s); split; first by rewrite lt_min hd hs.
    move=>t /andP [ht0 ht] j hj.
    have hMinL:Num.min d s<=d by rewrite ge_min lexx.
    have hMinR:Num.min d s<=s by rewrite ge_min lexx orbT.
    have htd:0<`|t|<d by rewrite ht0 /=; exact:(lt_le_trans ht hMinL).
    have hts:0<`|t|<s by rewrite ht0 /=; exact:(lt_le_trans ht hMinR).
    case:(eqVneq j m.+1)=>[->|hNe]; first exact:hNext t hts.
    have hjm:(j<=m)%N by move:hj; rewrite leq_eqVlt (negPf hNe) /= ltnS.
    exact:hb t htd j hjm.
have [d [hd hb]]:=hFinite i.
exists d; split=>// t ht.
have hBound:smooth_function_derivative_seminorm hD K i (err t f)<=e/2.
  apply:(@smooth_derivative_seminorm_least R X Y NX NY hNX hNY (fun _=>True) E D K i
    (smooth_function_derivative_seminorm hD K i) (smooth_function_derivative_seminorm_laws hD K i)
    (err t f) (e/2) (ltW hr))=>j hj x hx.
  exact:ltW (hb t ht j hj x hx).
apply:le_lt_trans hBound _; lra.
Qed.
End DifferenceQuotientSeminorm.
