(** Federer (1969), 4.1.9, p. 363: the printed
    positive-degree test-action restatement. Every original
    current is retained. All terms are actual compact tests
    agreeing with the printed smooth forms near its whole
    support; their existence is proved under exactly the
    original closed-cylinder properness. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP NormRegularity InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct AlternatingForms CurrentSpaces SmoothFunctionSpaceUP
  SmoothFunctionSpaceLaws SmoothTestSpaces SmoothTestEvaluation SmoothFormPullbackSealed
  SmoothCurrentExteriorDerivative CurrentTestExteriorDerivative CurrentTestExteriorAgreement
  CurrentTestNearSupportAgreement CurrentPushforwardUP CurrentPushforwardExistence
  CurrentHomotopyUP CurrentHomotopyGeometry CurrentHomotopySliceClass CurrentHomotopyCylinder CurrentHomotopyEndpointProper
  CurrentHomotopyTransgressionSealed CurrentHomotopyPositiveFormFormula
  CurrentHomotopyTestReplacementUP CurrentHomotopyTransgressionCompactTests.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section CurrentHomotopyPositiveTestFormula.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n nu j:nat.
Local Notation X := (R_n R n).
Local Notation Y := (R_n R nu).
Local Notation Z := (R_n R (1+n)%N).
Local Notation hNX := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Variable A:set R.
Variables (U:set X) (V:set Y).
Variables (f g:X->Y) (h:Z->Y).
Hypothesis hHomotopy:@is_smooth_current_homotopy R n nu A U V f g h.
Local Notation geometry := hHomotopy.1.
Local Notation hU := (@current_homotopy_source_open R n nu A U V f g h geometry).
Local Notation hV := (@current_homotopy_target_open R n nu A U V f g h geometry).
Local Notation endpoints := (@current_homotopy_endpoint_images R n nu A U V f g h geometry).
Local Notation classes := (@current_smooth_homotopy_endpoint_classes R n nu A U V f g h hHomotopy).
Local Notation EU := (@current_smooth_space R h2 n U hU j.+1).
Local Notation EV := (@current_smooth_space R h2 nu V hV j.+1).
Local Notation DU := (@current_test_space R h2 n U hU j.+1).
Local Notation DL := (@current_test_space R h2 n U hU j).
Local Notation DV := (@current_test_space R h2 nu V hV j.+1).
Local Notation hEU := (@current_smooth_space_laws R h2 n U hU j.+1).
Local Notation hEV := (@current_smooth_space_laws R h2 nu V hV j.+1).
Local Notation ev := (@current_smooth_value R h2 n U hU j.+1).
Local Notation value := (@current_test_value R h2 n U hU j.+1).
Local Notation Inc := (smooth_test_inclusion hEV).
Local Notation PullF := (@SmoothFormPullback.operator R h2 n nu j.+1 U V hU hV f endpoints.1 classes.1).
Local Notation PullG := (@SmoothFormPullback.operator R h2 n nu j.+1 U V hU hV g endpoints.2 classes.2).
Local Notation K := (@CurrentHomotopyTransgression.value R h2 n nu j.+1 A U V f g h hHomotopy).
Local Notation KL := (@CurrentHomotopyTransgression.value R h2 n nu j A U V f g h hHomotopy).
Local Notation d := (@smooth_current_exterior_derivative R h2 nu j.+1 V hV).
Local Notation dU := (@smooth_current_exterior_derivative R h2 n j U hU).
Local Notation td := (@current_test_exterior_derivative R h2 n j U hU).
Variable T:@current_space R h2 n U hU j.+1.
Local Notation support := (@current_support R h2 n U hU j.+1 T).
Local Notation action := (@current_value R h2 n U hU j.+1 T).
Local Notation agreeF := (@is_current_pullback_test_replacement R h2 n nu j.+1 U V hU hV T f endpoints.1 classes.1).
Local Notation agreeG := (@is_current_pullback_test_replacement R h2 n nu j.+1 U V hU hV T g endpoints.2 classes.2).
Local Notation agreeK := (@is_current_homotopy_test_replacement R h2 n nu j.+1 j.+1 A U V f g h hHomotopy T).
Local Notation agreeL := (@is_current_homotopy_test_replacement R h2 n nu j.+1 j A U V f g h hHomotopy T).

(** Source for [current_homotopy_positive_test_formula]:
    T(g#psi-f#psi)=T(K(d psi)+d(K psi)) for every
    admissible compact choice, Federer 4.1.9, p. 363.
    The displayed actions use actual source tests, so no
    action of a general current on noncompact forms is assumed. *)
Theorem current_homotopy_positive_test_formula (psi:DV)
    (betaG betaF betaK:DU) (betaL:DL):
  agreeG psi betaG->agreeF psi betaF->
  agreeK (d (Inc psi)) betaK->agreeL (Inc psi) betaL->
  action (betaG-betaF)=action (betaK+td betaL).
Proof.
move=>[WG [hWG [hTG [hGU hG]]]] [WF [hWF [hTF [hFU hF]]]]
  [WK [hWK [hTK [hKU hK]]]] [WL [hWL [hTL [hLU hL]]]].
pose W:=((WG `&` WF) `&` WK) `&` WL.
apply:(@current_test_near_support_values_equal R h2 n j.+1 U hU T
  (betaG-betaF) (betaK+td betaL) W (openI (openI (openI hWG hWF) hWK) hWL)).
- move=>x hx;exact:conj (conj (conj (hTG x hx) (hTF x hx)) (hTK x hx)) (hTL x hx).
- move=>x [[[hxG hxF] hxK] hxL].
  have hDerivative:=@current_test_exterior_local_agreement R h2 n j U hU betaL (KL (Inc psi))
    WL hWL hLU hL x hxL.
  have hLeft:value (betaG-betaF) x=value betaG x-value betaF x.
    exact:(congr1 (fun z:X->A_m X R^o j.+1=>z x)
      (linearB (smooth_test_values_hom hEU) betaG betaF)).
  have hRight:value (betaK+td betaL) x=value betaK x+value (td betaL) x.
    exact:(congr1 (fun z:X->A_m X R^o j.+1=>z x)
      (linearD (smooth_test_values_hom hEU) betaK (td betaL))).
  have hForm:=congr1 (fun z:EU=>ev z x)
    (@current_homotopy_positive_form_formula R h2 n nu j A U V f g h hHomotopy (Inc psi)).
  have hFormLeft:ev (PullG (Inc psi)-PullF (Inc psi)) x=ev (PullG (Inc psi)) x-ev (PullF (Inc psi)) x.
    exact:(congr1 (fun z:X->A_m X R^o j.+1=>z x)
      (linearB (smooth_function_values_hom hEU) (PullG (Inc psi)) (PullF (Inc psi)))).
  have hFormRight:ev (K (d (Inc psi))+dU (KL (Inc psi))) x=
      ev (K (d (Inc psi))) x+ev (dU (KL (Inc psi))) x.
    exact:(congr1 (fun z:X->A_m X R^o j.+1=>z x)
      (linearD (smooth_function_values_hom hEU) (K (d (Inc psi))) (dU (KL (Inc psi))))).
  rewrite hFormLeft hFormRight in hForm.
  rewrite hLeft hRight (hG x hxG) (hF x hxF) (hK x hxK) hDerivative.
  exact:hForm.
Qed.

(** Source for [current_homotopy_positive_test_formula_exists]:
    all four compact representatives in the printed restatement
    exist and satisfy it under exactly the original properness,
    Federer 4.1.9, p. 363. Whole-source compactness,
    finite mass and representability are not added. *)
Theorem current_homotopy_positive_test_formula_exists
    (hProper:@is_current_homotopy_proper R h2 n nu j.+1 A U V f g h geometry T) (psi:DV):
  exists (betaG betaF betaK:DU) (betaL:DL),
    agreeG psi betaG /\ agreeF psi betaF /\ agreeK (d (Inc psi)) betaK /\
    agreeL (Inc psi) betaL /\ action (betaG-betaF)=action (betaK+td betaL).
Proof.
have[betaG hG]:=@current_pushforward_test_replacement_exists R h2 n nu j.+1 U V hU hV T
  g endpoints.2 classes.2 (@current_homotopy_end_proper R h2 n nu j.+1 A U V f g h geometry T hProper) psi.
have[betaF hF]:=@current_pushforward_test_replacement_exists R h2 n nu j.+1 U V hU hV T
  f endpoints.1 classes.1 (@current_homotopy_start_proper R h2 n nu j.+1 A U V f g h geometry T hProper) psi.
have[betaK hK]:=@current_homotopy_test_replacement_exists R h2 n nu j.+1 j.+1 A U V f g h
  hHomotopy T hProper (@current_test_exterior_derivative R h2 nu j.+1 V hV psi).
rewrite current_test_exterior_derivative_inclusion in hK.
have[betaL hL]:=@current_homotopy_test_replacement_exists R h2 n nu j.+1 j A U V f g h
  hHomotopy T hProper psi.
exists betaG,betaF,betaK,betaL;split=>//;split=>//;split=>//;split=>//.
exact:current_homotopy_positive_test_formula hG hF hK hL.
Qed.
End CurrentHomotopyPositiveTestFormula.
