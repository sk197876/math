(** Federer (1969), 4.1.1, p. 346: one
    compact set contains the supports of the
    test quotient errors for all sufficiently
    small increments. A finite-dimensional compact
    ball supplies the bound, including empty
    supports and zero directions. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP NormOpenDomainLaws LinearBasis
  NormClassZeroWhole NormCompactFunctionBound FiniteNormMetricCompactness ContinuousMultilinearSealed
  SmoothCompactSet SmoothCompactTranslationTube SmoothFunctionSpaceUP SmoothFunctionSpaceLaws SmoothFunctionSupport SmoothFunctionDerivativesUP
  SmoothDirectionalDerivativeUP SmoothDirectionalSupport SmoothGlobalTranslationUP SmoothDifferenceQuotientJets.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section DifferenceErrorSupport.
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
Local Notation Z := (fun k=>@ContinuousMultilinear.space R k X Y NX NY hNX hNY).
Variable D:forall k,X->Hom E (Z k).
Hypothesis hD:@is_smooth_function_derivatives R X Y NX NY hNX hNY (fun _=>True) E ev D.
Variable v:X.
Variable P:Hom E E.
Hypothesis hP:@is_smooth_directional_derivative R X Y NX NY hNX hNY (fun _=>True) E ev D v P.
Variable L:X->Hom E E.
Hypothesis hL:forall c,is_smooth_global_translation ev c (L c).
Local Notation err := (@smooth_difference_quotient_error R X E v P L).
Local Notation support := (@smooth_function_support R X Y NX hNX (fun _=>True) E ev).

(** Source for [smooth_difference_error_value]: the
    represented error has exactly the printed
    pointwise quotient-minus-derivative value,
    supporting Federer 4.1.1, p. 346. *)
Lemma smooth_difference_error_value t f x:
  ev (err t f) x=t^-1*:(ev f (x+t*:v)-ev f x)-ev (P f) x.
Proof.
pose H:=smooth_function_values_hom hE.
have hOuter:ev (err t f)=ev (t^-1*:(L (t*:v) f-f))-ev (P f).
  exact:(linearB (hom_as_linear H) (t^-1*:(L (t*:v) f-f)) (P f)).
have hScale:ev (t^-1*:(L (t*:v) f-f))=t^-1*:ev (L (t*:v) f-f):=
  linearZ_LR (hom_as_linear H) t^-1 (L (t*:v) f-f).
have hInner:ev (L (t*:v) f-f)=ev (L (t*:v) f)-ev f.
  exact:(linearB (hom_as_linear H) (L (t*:v) f) f).
have hValues:ev (err t f)=t^-1*:(ev (L (t*:v) f)-ev f)-ev (P f).
  by rewrite hOuter hScale hInner.
have hAt:=congr1 (fun F:X->Y=>F x) hValues.
change (ev (err t f) x=t^-1*:(ev (L (t*:v) f) x-ev f x)-ev (P f) x) in hAt.
by rewrite hL in hAt.

Qed.

(** Source for [smooth_difference_error_common_support]:
    all quotient errors for |t|<=1 have support
    in one compact C, supporting the D-limit
    asserted in Federer 4.1.1, p. 346. *)
Theorem smooth_difference_error_common_support (K:smooth_compact_set hNX (fun _=>True)) f:
  support f `<=` smooth_compact_carrier K ->
  exists C:smooth_compact_set hNX (fun _=>True),forall t:R,`|t|<=1 ->
    support (err t f) `<=` smooth_compact_carrier C.
Proof.
move=>hSupport.
have [C [hKC hShift]]:=@smooth_compact_translation_tube R X NX hNX d b hb K v.
have hDerivative:=@smooth_directional_derivative_preserves_compact_support R X Y NX NY hNX hNY
  (fun _=>True) (fun x _=>norm_full_domain_interior NX x) E ev hE D hD v P hP K f hSupport.
exists C=>t ht; apply:(smooth_function_compact_support_iff hE C (err t f)).2=>x hx.
have hNoK:~smooth_compact_carrier K x by move=>hKx; exact:hx (hKC x hKx).
have hNoShift:~smooth_compact_carrier K (x+t*:v).
  move=>hKx; exact:hx (hShift t ht x hKx).
rewrite smooth_difference_error_value
  ((smooth_function_compact_support_iff hE K f).1 hSupport (x+t*:v) hNoShift)
  ((smooth_function_compact_support_iff hE K f).1 hSupport x hNoK)
  ((smooth_function_compact_support_iff hE K (P f)).1 hDerivative x hNoK)
  subrr scaler0 subrr; reflexivity.
Qed.
End DifferenceErrorSupport.
