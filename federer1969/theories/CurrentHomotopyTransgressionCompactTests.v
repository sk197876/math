(** Federer (1969), 4.1.9, p. 363: prove that the
    original homotopy forms have genuine compact test
    replacements near the whole support of every current
    satisfying the printed cylinder properness. The original
    cutoff and smooth homotopy operator remain opaque. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP NormClassOneUP NormRegularity InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct FiniteCoordinates AlternatingForms CurrentCoefficientNorms CurrentSpaces
  SmoothCompactSet SmoothFunctionSpaceUP SmoothFunctionSupport SmoothTestSpaces SmoothTestEvaluation
  SmoothCutoffReplacement SmoothLocalAgreementSeminorm
  CurrentHomotopyUP CurrentHomotopyCylinder CurrentHomotopyTransgressionSealed CurrentHomotopyAvoidCompact
  CurrentHomotopyCompactTestLocus CurrentHomotopyTransgressionAvoidCompact CurrentHomotopyTestReplacementUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section CurrentHomotopyTransgressionCompactTests.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n nu k j:nat.
Local Notation X := (R_n R n).
Local Notation Y := (R_n R nu).
Local Notation Z := (R_n R (1+n)%N).
Local Notation NX := (inner_norm (@euclidean_inner_productP R n)).
Local Notation NY := (inner_norm (@euclidean_inner_productP R nu)).
Local Notation hNX := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation hNY := (inner_norm_real_norm (@euclidean_inner_productP R nu)).
Local Notation PN := (@current_form_comass R h2 n j).
Local Notation hPN := (@current_form_comass_real_norm R h2 n j).
Variable A:set R.
Variables (U:set X) (V:set Y).
Variables (f g:X->Y) (h:Z->Y).
Hypothesis hHomotopy:@is_smooth_current_homotopy R n nu A U V f g h.
Local Notation geometry := hHomotopy.1.
Local Notation hU := (@current_homotopy_source_open R n nu A U V f g h geometry).
Local Notation hV := (@current_homotopy_target_open R n nu A U V f g h geometry).
Local Notation F := (@current_smooth_space R h2 nu V hV (1+j)).
Local Notation fv := (@current_smooth_value R h2 nu V hV (1+j)).
Local Notation hF := (@current_smooth_space_laws R h2 nu V hV (1+j)).
Local Notation E := (@current_smooth_space R h2 n U hU j).
Local Notation ev := (@current_smooth_value R h2 n U hU j).
Local Notation hE := (@current_smooth_space_laws R h2 n U hU j).
Local Notation D := (@current_test_space R h2 n U hU j).
Local Notation value := (@current_test_value R h2 n U hU j).
Local Notation KH := (@CurrentHomotopyTransgression.value R h2 n nu j A U V f g h hHomotopy).
Variable T:@current_space R h2 n U hU k.
Local Notation support := (@current_support R h2 n U hU k T).
Hypothesis hProper:@is_current_homotopy_proper R h2 n nu k A U V f g h geometry T.
Local Notation agree := (@is_current_homotopy_test_replacement R h2 n nu k j A U V f g h hHomotopy T).

(** Source for [current_homotopy_transgression_compact_tests]:
    a common compact target support gives one actual linear
    test replacement and one neighbourhood of the whole
    current support, supporting the original restatement in
    Federer 4.1.9, p. 363. Input T need not have
    compact support or a measure representation. *)
Theorem current_homotopy_transgression_compact_tests (K:smooth_compact_set hNY V):
  exists Q:Hom F D,exists W:set X,@open (real_norm_metric_space hNX) W /\
    support `<=` W /\ W `<=` U /\
    forall psi:F,@smooth_function_support R Y (A_m Y R^o (1+j)) NY hNY V F fv psi `<=` smooth_compact_carrier K->
      forall x,W x->value (Q psi) x=ev (KH psi) x.
Proof.
pose L:=@current_homotopy_compact_test_index R h2 n nu k A U V f g h geometry T hProper K.
pose replace:=@smooth_cutoff_replacement R X (A_m X R^o j) NX PN hNX hPN n
  (@coordinate_basis R n) (@coordinate_basisP R n) U hU E ev hE L.
pose Q:=hom_comp replace KH.
have[W [hW [hLW [hWU hAgreement]]]]:=@smooth_cutoff_replacement_agrees_near_compact
  R X (A_m X R^o j) NX PN hNX hPN n (@coordinate_basis R n) (@coordinate_basisP R n)
  U hU E ev hE L.
pose Avoid:=@current_homotopy_avoid_compact R n nu A U V f g h geometry K.
have hAvoid:@open (real_norm_metric_space hNX) Avoid:=
  @current_homotopy_avoid_compact_open R n nu A U V f g h geometry K
    (norm_class_continuous (hHomotopy.2 0%N)).
have hZero psi (hPsi:@smooth_function_support R Y (A_m Y R^o (1+j)) NY hNY V F fv psi `<=` smooth_compact_carrier K):
    forall x,Avoid x->ev (KH psi) x=0.
  exact:(@current_homotopy_transgression_avoids_compact R h2 n nu j A U V f g h hHomotopy K psi hPsi).
exists Q,(W `|` Avoid);split;first exact:openU hW hAvoid.
split.
- move=>x hx;have[hL|hOff]:=@current_homotopy_support_compact_or_avoid R h2 n nu k A U V f g h geometry T K x hx.
  + left;exact:hLW x hL.
  + by right.
- split;first by move=>x [hx|hx];[exact:hWU x hx|exact:hx.1].
  move=>psi hPsi x [hx|hx].
  + exact:hAgreement (KH psi) x hx.
  + have hInputZero:=hZero psi hPsi.
    have hInputAvoid:=@smooth_support_avoids_open_zero_set R X (A_m X R^o j) NX hNX U E ev
      (KH psi) Avoid hAvoid hInputZero x hx.
    have hShrink:=@smooth_cutoff_replacement_support_subset R X (A_m X R^o j) NX PN hNX hPN n
      (@coordinate_basis R n) (@coordinate_basisP R n) U hU E ev hE L (KH psi).
    have hTestZero:value (Q psi) x=0.
      apply:contrapT=>hNonzero;apply:hInputAvoid;apply:hShrink.
      split;first exact:hx.1.
      exact:(@subset_closure (real_norm_metric_space hNX) _ x hNonzero).
    by rewrite hTestZero (hInputZero x hx).
Qed.

(** Source for [current_homotopy_test_replacement_exists]:
    every original target test admits a genuine source test
    agreeing with its homotopy form near all spt T,
    Federer 4.1.9, p. 363. Existence follows from
    exactly the original closed-cylinder properness. *)
Theorem current_homotopy_test_replacement_exists
    (psi:@current_test_space R h2 nu V hV (1+j)):
  exists beta:D,agree (smooth_test_inclusion hF psi) beta.
Proof.
have[K hK]:=smooth_test_support_bound hF psi.
have[Q [W [hW [hTW [hWU hAgreement]]]]]:=current_homotopy_transgression_compact_tests K.
exists (Q (smooth_test_inclusion hF psi)),W;split=>//;split=>//;split=>//.
exact:hAgreement (smooth_test_inclusion hF psi) hK.
Qed.
End CurrentHomotopyTransgressionCompactTests.
