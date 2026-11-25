(** Federer (1969), 4.1.1, p. 346: the
    difference-quotient error tends to zero uniformly
    on each compact set in every derivative.
    All derivatives and translations are actual
    operators already proved to exist. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP NormOpenDomainLaws NormRegularity ContinuousMultilinearUP
  ContinuousMultilinearSealed ContinuousMultilinearNorm SmoothCompactSet SmoothFunctionSpaceUP
  SmoothFunctionDerivativesUP SmoothDirectionalDerivativeUP SmoothGlobalTranslationUP
  SmoothGlobalTranslationDerivatives SmoothHigherDerivativeRegularity SmoothDerivativeDirectionalField
  NormCompactDirectionalQuotient.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Section DifferenceQuotientJets.
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
Local Notation hZ := (fun k=>@ContinuousMultilinear.laws R k X Y NX NY hNX hNY).
Variable D:forall k,X->Hom E (Z k).
Hypothesis hD:@is_smooth_function_derivatives R X Y NX NY hNX hNY (fun _=>True) E ev D.
Variable v:X.
Variable P:Hom E E.
Hypothesis hP:@is_smooth_directional_derivative R X Y NX NY hNX hNY (fun _=>True) E ev D v P.
Variable L:X->Hom E E.
Hypothesis hL:forall c,is_smooth_global_translation ev c (L c).

(** Source for [smooth_difference_quotient_error]: the
    original quotient minus D_v phi in Federer
    4.1.1, p. 346. Its value at zero
    is irrelevant to the punctured limit. *)
Definition smooth_difference_quotient_error (t:R) (f:E):E:=
  t^-1*:(L (t*:v) f-f)-P f.

(** Source for [smooth_difference_quotient_jet]: each actual
    derivative of the error tends to zero
    uniformly on a compact K, supporting the
    D-topology limit in Federer 4.1.1, p. 346. *)
Theorem smooth_difference_quotient_jet j f (K:smooth_compact_set hNX (fun _=>True)):
  forall e:R,0<e ->exists d:R,0<d /\ forall t,
    0<`|t|<d ->forall x,smooth_compact_carrier K x ->
      @ZN j (@D j x (smooth_difference_quotient_error t f))<e.
Proof.
move=>e he.
pose hNj:=continuous_multilinear_norm_is_norm hNY (hZ j).
have hReg:=@smooth_higher_derivative_field_regular R X Y NX NY hNX hNY
  (fun _=>True) E ev hE j D hD f 1%N.
have [d [hd hb]]:=@norm_compact_directional_quotient R X (Z j) NX (@ZN j) hNX hNj
  (fun _=>True) (smooth_compact_carrier K) (fun x=>@D j x f) hReg
  (smooth_compact_is_compact K) (fun _ _=>Logic.I) v e he.
exists d; split=>// t ht x hx.
have [M [hM hMv]]:=@smooth_derivative_directional_differential R X Y NX NY hNX hNY
  (fun _=>True) (fun x _=>norm_full_domain_interior NX x) E ev D hD v P hP j f x Logic.I.
have hBound:=hb x hx t ht M hM.
have hJet:@D j x (smooth_difference_quotient_error t f)=
  t^-1*:(@D j (x+t*:v) f-@D j x f)-M v.
  have hScale:@D j x (t^-1*:(L (t*:v) f-f))=
    t^-1*:(@D j x (L (t*:v) f-f)):=linearZ_LR (hom_as_linear (@D j x)) t^-1 (L (t*:v) f-f).
  have hOuter:@D j x (smooth_difference_quotient_error t f)=
    @D j x (t^-1*:(L (t*:v) f-f))-@D j x (P f).
    exact:(linearB (hom_as_linear (@D j x)) (t^-1*:(L (t*:v) f-f)) (P f)).
  have hInner:@D j x (L (t*:v) f-f)=@D j x (L (t*:v) f)-@D j x f.
    exact:(linearB (hom_as_linear (@D j x)) (L (t*:v) f) f).
  rewrite hOuter hScale hInner -hMv.
  by rewrite (@smooth_global_translation_derivatives R X Y NX NY hNX hNY E ev D hD
    (t*:v) (L (t*:v)) (hL (t*:v))).
by rewrite hJet.
Qed.
End DifferenceQuotientJets.
