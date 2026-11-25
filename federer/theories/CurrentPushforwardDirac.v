(** Federer (1969), 4.1.7, p. 359:
    the original point current pushes forward
    to the point current at its image.
    Its singleton support is proper for
    every actual smooth map. This supplies
    the printed half-line identity f#delta_b^U=delta_b^R. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets reals topology.
From Federer Require Import CurrentEvaluation Hom RealNormUP NormMetric NormDifferentialUP NormRegularity InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct AlternatingForms AlternatingZero AlternatingDual
  CurrentSpaces CurrentCoefficientNorms CurrentDirac DiracCurrentBounds CurrentProperSupport CurrentProperSupportRestriction
  CurrentPushforwardUP CurrentPushforwardExistence CurrentPushforwardSealed CurrentMapDifferential
  SmoothFormPullbackUP SmoothFormPullbackSealed SmoothCompactSet SmoothTestSpaces SmoothTestEvaluation.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [current_pullback_zero_coefficient]:
    the original pullback in degree zero
    preserves the scalar coefficient, supporting
    Federer 4.1.7, p. 359, by
    1.4.1, pp. 17–18, and 4.1.6,
    p. 354. *)
Lemma current_pullback_zero_coefficient (K:fieldType) (X Y:lmodType K)
    (L:Hom X Y) (a:A_m Y K^o 0):
  zero_form_value (A_m_dual (hom_as_linear L) a)=zero_form_value a.
Proof.
have hZero:A_m_dual (hom_as_linear L) a=@zero_form K X K^o (zero_form_value a).
  rewrite -{1}(zero_form_valueK a).
  apply:form_ext=>t;by rewrite A_m_dualE !zero_formE.
by rewrite hZero zero_formK.
Qed.

Section CurrentPushforwardDirac.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables v n:nat.
Local Notation X := (R_n R v).
Local Notation Y := (R_n R n).
Local Notation NX := (inner_norm (@euclidean_inner_productP R v)).
Local Notation NY := (inner_norm (@euclidean_inner_productP R n)).
Local Notation hNX := (inner_norm_real_norm (@euclidean_inner_productP R v)).
Local Notation hNY := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Variables (U:set X) (V:set Y).
Hypothesis hU:forall x,U x->norm_domain_interior NX U x.
Arguments hU : clear implicits.
Hypothesis hV:forall y,V y->norm_domain_interior NY V y.
Arguments hV : clear implicits.
Variable c:X.
Hypothesis hc:U c.
Local Notation delta := (@dirac_current R h2 v U hU c).
Variable f:X->Y.
Hypothesis hImage:forall x,U x->V (f x).
Arguments hImage : clear implicits.
Hypothesis hf:norm_class_all_orders hNX hNY U f.
Local Notation E := (@current_smooth_space R h2 n V hV 0%N).
Local Notation F := (@current_smooth_space R h2 v U hU 0%N).
Local Notation hE := (@current_smooth_space_laws R h2 n V hV 0%N).
Local Notation ev := (@current_smooth_value R h2 n V hV 0%N).
Local Notation fv := (@current_smooth_value R h2 v U hU 0%N).
Local Notation pull := (@SmoothFormPullback.operator R h2 v n 0%N U V hU hV f hImage hf).

(** Source for [current_point_support_proper]:
    every original smooth map is proper
    on the singleton support of a point
    current, supporting Federer 4.1.7, p. 359.
    No whole-source properness is required. *)
Theorem current_point_support_proper:
  @is_current_proper_on_support R h2 v n 0%N U hU V delta f hImage.
Proof.
apply:(@current_proper_support_compact_loci R h2 v n U hU V f hImage 0%N delta).2=>K.
rewrite (@dirac_current_support R h2 v U hU c hc).
case:(pselect (smooth_compact_carrier K (f c)))=>hK.
- have hEqual:[set x:X|[set c] x /\smooth_compact_carrier K (f x)]=[set c].
    apply/seteqP;split;first by move=>x hx;exact:hx.1.
    move=>x ->;by split.
  rewrite hEqual;exact:compact_set1.
- have hEqual:[set x:X|[set c] x /\smooth_compact_carrier K (f x)]=set0.
    apply/seteqP;split;last by [].
    move=>x [-> hx];exact:hK hx.
  rewrite hEqual;exact:compact0.
Qed.

(** Source for [current_pushforward_dirac]: the
    actual original f#delta_c is delta_(f(c)),
    supporting the printed half-line boundary
    pushforward in Federer 4.1.7, p. 359.
    Source and target dimensions may be zero. *)
Theorem current_pushforward_dirac:
  @CurrentPushforward.value R h2 v n 0%N U V hU hV delta f hImage hf current_point_support_proper=
    @dirac_current R h2 n V hV (f c).
Proof.
apply:(@current_values_extensional R h2 n 0%N V hV)=>phi.
have [alpha [W [hW [hTW [hWU hAgreement]]]]]:=
  @current_pushforward_test_replacement_exists R h2 v n 0%N U V hU hV delta f hImage hf
    current_point_support_proper phi.
have hReplacement:@is_current_pullback_test_replacement R h2 v n 0%N U V hU hV delta f hImage hf phi alpha.
  exists W;by split=>//;split=>//;split.
have hValue:=@CurrentPushforward.laws R h2 v n 0%N U V hU hV delta f hImage hf
  current_point_support_proper phi alpha hReplacement.
have hSupport:@current_support R h2 v U hU 0%N delta c.
  rewrite (@dirac_current_support R h2 v U hU c hc);by [].
have hAt:=@hAgreement c (@hTW c hSupport).
have hPull:=@smooth_form_pullback_values R v n 0%N U V E F ev fv f pull
  (@SmoothFormPullback.laws R h2 v n 0%N U V hU hV f hImage hf)
  (smooth_test_inclusion hE phi) c (@current_map_differential R v n U f c) hc
  (@current_map_differential_actual R v n U f hf c hc).
rewrite hValue !dirac_current_evaluation hAt hPull current_pullback_zero_coefficient;by [].
Qed.
End CurrentPushforwardDirac.
