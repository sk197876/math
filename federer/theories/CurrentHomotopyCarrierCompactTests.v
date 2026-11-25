(** Federer (1969), 4.1.18, p. 374: compact
    kernel parameters give compact representatives of
    the original transgression near their entire strip.
    This carrier version is the preceding 4.1.9
    cutoff proof with its compact locus supplied
    explicitly. No current representation is used. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  functions classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP
  NormRegularity InnerNorm HilbertFormCompactness GrassmannAbbreviations
  EuclideanInnerProduct FiniteCoordinates AlternatingForms CurrentSpaces
  CurrentCoefficientNorms SmoothCompactSet SmoothFunctionSpaceUP SmoothFunctionSupport
  SmoothTestSpaces SmoothTestEvaluation SmoothCutoffReplacement
  SmoothLocalAgreementSeminorm CurrentHomotopyUP CurrentHomotopyDomain
  CurrentHomotopyTransgressionSealed CurrentHomotopyAvoidCompact
  CurrentHomotopyTransgressionAvoidCompact.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section CurrentHomotopyCarrierCompactTests.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n nu j:nat.
Local Notation X:=(R_n R n).
Local Notation Y:=(R_n R nu).
Local Notation NX:=(inner_norm (@euclidean_inner_productP R n)).
Local Notation NY:=(inner_norm (@euclidean_inner_productP R nu)).
Local Notation hNX:=(inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation hNY:=(inner_norm_real_norm (@euclidean_inner_productP R nu)).
Variable A:set R.
Variables (U:set X) (V:set Y).
Variables (f g:X->Y) (h:R_n R (1+n)%N->Y).
Hypothesis hH:@is_smooth_current_homotopy R n nu A U V f g h.
Local Notation hU:=(@current_homotopy_source_open R n nu A U V f g h hH.1).
Local Notation hV:=(@current_homotopy_target_open R n nu A U V f g h hH.1).
Local Notation F:=(@current_smooth_space R h2 nu V hV (1+j)%N).
Local Notation fv:=(@current_smooth_value R h2 nu V hV (1+j)%N).
Local Notation E:=(@current_smooth_space R h2 n U hU j).
Local Notation ev:=(@current_smooth_value R h2 n U hU j).
Local Notation hE:=(@current_smooth_space_laws R h2 n U hU j).
Local Notation D:=(@current_test_space R h2 n U hU j).
Local Notation value:=(@current_test_value R h2 n U hU j).
Local Notation KH:=(@CurrentHomotopyTransgression.value R h2 n nu j A U V f g h hH).
Variable K:smooth_compact_set hNY V.
Local Notation Avoid:=(@current_homotopy_avoid_compact R n nu A U V f g h hH.1 K).
Variable L:smooth_compact_set hNX U.
Variable C:set X.
Hypothesis hCover:C `<=` (smooth_compact_carrier L `|` Avoid).

(** Source for [current_homotopy_carrier_compact_tests]:
    the original compact-cutoff and whole-path
    avoidance proof of 4.1.9, p. 363, applied
    to the compact-kernel strip of 4.1.18,
    p. 374. Empty carriers are allowed. *)
Theorem current_homotopy_carrier_compact_tests:
  exists Q:Hom F D,exists W:set X,@open (real_norm_metric_space hNX) W /\
    C `<=` W /\W `<=` U /\
    forall omega:F,@smooth_function_support R Y (A_m Y R^o (1+j)%N)
      NY hNY V F fv omega `<=` smooth_compact_carrier K->
      forall x,W x->value (Q omega) x=ev (KH omega) x.
Proof.
pose Replace:=@smooth_cutoff_replacement R X (A_m X R^o j) NX
  (@current_form_comass R h2 n j) hNX (@current_form_comass_real_norm R h2 n j)
  n (@coordinate_basis R n) (@coordinate_basisP R n) U hU E ev hE L.
have[W [hW [hLW [hWU hAgreement]]]]:=
  @smooth_cutoff_replacement_agrees_near_compact R X (A_m X R^o j) NX
    (@current_form_comass R h2 n j) hNX (@current_form_comass_real_norm R h2 n j)
    n (@coordinate_basis R n) (@coordinate_basisP R n) U hU E ev hE L.
have hAvoid:@open (real_norm_metric_space hNX) Avoid:=
  @current_homotopy_avoid_compact_open R n nu A U V f g h hH.1 K
    (norm_class_continuous (hH.2 0%N)).
exists (hom_comp Replace KH),(W `|` Avoid);split;first exact:openU hW hAvoid.
split.
- move=>x hx;case:(@hCover x hx)=>[hxL|hxAvoid].
  + left;exact:@hLW x hxL.
  + by right.
split;first by move=>x [hx|hx];[exact:@hWU x hx|exact:hx.1].
move=>omega hOmega x [hxW|hxAvoid].
- exact:(@hAgreement (KH omega) x hxW).
- have hZero:=@current_homotopy_transgression_avoids_compact R h2 n nu j
    A U V f g h hH K omega hOmega.
  have hInputAvoid:=@smooth_support_avoids_open_zero_set R X (A_m X R^o j)
    NX hNX U E ev (KH omega) Avoid hAvoid hZero x hxAvoid.
  have hShrink:=@smooth_cutoff_replacement_support_subset R X (A_m X R^o j) NX
    (@current_form_comass R h2 n j) hNX (@current_form_comass_real_norm R h2 n j)
    n (@coordinate_basis R n) (@coordinate_basisP R n) U hU E ev hE L (KH omega).
  have hTestZero:value (Replace (KH omega)) x=0.
    apply:contrapT=>hNonzero;apply:hInputAvoid;apply:hShrink.
    split;first exact:hxAvoid.1.
    exact:(@subset_closure (real_norm_metric_space hNX) _ x hNonzero).
  by rewrite hTestZero (@hZero x hxAvoid).
Qed.
End CurrentHomotopyCarrierCompactTests.
