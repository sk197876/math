(** Federer (1969), 4.1.9, p. 363: the printed
    degree-zero test-action restatement. Every original
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
  CurrentHomotopyTransgressionSealed CurrentHomotopyZeroFormFormula
  CurrentHomotopyTestReplacementUP CurrentHomotopyTransgressionCompactTests.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section CurrentHomotopyZeroTestFormula.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n nu:nat.
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
Local Notation EU := (@current_smooth_space R h2 n U hU 0%N).
Local Notation EV := (@current_smooth_space R h2 nu V hV 0%N).
Local Notation DU := (@current_test_space R h2 n U hU 0%N).
Local Notation DV := (@current_test_space R h2 nu V hV 0%N).
Local Notation hEU := (@current_smooth_space_laws R h2 n U hU 0%N).
Local Notation hEV := (@current_smooth_space_laws R h2 nu V hV 0%N).
Local Notation ev := (@current_smooth_value R h2 n U hU 0%N).
Local Notation value := (@current_test_value R h2 n U hU 0%N).
Local Notation Inc := (smooth_test_inclusion hEV).
Local Notation PullF := (@SmoothFormPullback.operator R h2 n nu 0%N U V hU hV f endpoints.1 classes.1).
Local Notation PullG := (@SmoothFormPullback.operator R h2 n nu 0%N U V hU hV g endpoints.2 classes.2).
Local Notation K := (@CurrentHomotopyTransgression.value R h2 n nu 0%N A U V f g h hHomotopy).
Local Notation d := (@smooth_current_exterior_derivative R h2 nu 0%N V hV).
Variable T:@current_space R h2 n U hU 0%N.
Local Notation support := (@current_support R h2 n U hU 0%N T).
Local Notation action := (@current_value R h2 n U hU 0%N T).
Local Notation agreeF := (@is_current_pullback_test_replacement R h2 n nu 0%N U V hU hV T f endpoints.1 classes.1).
Local Notation agreeG := (@is_current_pullback_test_replacement R h2 n nu 0%N U V hU hV T g endpoints.2 classes.2).
Local Notation agreeK := (@is_current_homotopy_test_replacement R h2 n nu 0%N 0%N A U V f g h hHomotopy T).


(** Source for [current_homotopy_zero_test_formula]:
    T(g#psi-f#psi)=T(K(d psi)) in degree zero for
    every admissible compact choice, Federer 4.1.9, p. 363.
    The lower-degree summand is absent, as printed. *)
Theorem current_homotopy_zero_test_formula (psi:DV) (betaG betaF betaK:DU):
  agreeG psi betaG->agreeF psi betaF->agreeK (d (Inc psi)) betaK->
  action (betaG-betaF)=action betaK.
Proof.
move=>[WG [hWG [hTG [hGU hG]]]] [WF [hWF [hTF [hFU hF]]]]
  [WK [hWK [hTK [hKU hK]]]].
pose W:=(WG `&` WF) `&` WK.
apply:(@current_test_near_support_values_equal R h2 n 0%N U hU T
  (betaG-betaF) betaK W (openI (openI hWG hWF) hWK)).
- move=>x hx;exact:conj (conj (hTG x hx) (hTF x hx)) (hTK x hx).
- move=>x [[hxG hxF] hxK].
  have hLeft:value (betaG-betaF) x=value betaG x-value betaF x.
    exact:(congr1 (fun z:X->A_m X R^o 0%N=>z x)
      (linearB (smooth_test_values_hom hEU) betaG betaF)).
  have hForm:=congr1 (fun z:EU=>ev z x)
    (@current_homotopy_zero_form_formula R h2 n nu A U V f g h hHomotopy (Inc psi)).
  have hFormLeft:ev (PullG (Inc psi)-PullF (Inc psi)) x=ev (PullG (Inc psi)) x-ev (PullF (Inc psi)) x.
    exact:(congr1 (fun z:X->A_m X R^o 0%N=>z x)
      (linearB (smooth_function_values_hom hEU) (PullG (Inc psi)) (PullF (Inc psi)))).
  rewrite hFormLeft in hForm.
  rewrite hLeft (hG x hxG) (hF x hxF) (hK x hxK).
  exact:hForm.
Qed.

(** Source for [current_homotopy_zero_test_formula_exists]:
    all compact representatives in the printed degree-zero
    restatement exist and satisfy it under the original
    closed-cylinder properness, Federer 4.1.9, p. 363.
    No negative-degree current or boundary is introduced. *)
Theorem current_homotopy_zero_test_formula_exists
    (hProper:@is_current_homotopy_proper R h2 n nu 0%N A U V f g h geometry T) (psi:DV):
  exists betaG betaF betaK:DU,
    agreeG psi betaG /\ agreeF psi betaF /\ agreeK (d (Inc psi)) betaK /\
    action (betaG-betaF)=action betaK.
Proof.
have[betaG hG]:=@current_pushforward_test_replacement_exists R h2 n nu 0%N U V hU hV T
  g endpoints.2 classes.2 (@current_homotopy_end_proper R h2 n nu 0%N A U V f g h geometry T hProper) psi.
have[betaF hF]:=@current_pushforward_test_replacement_exists R h2 n nu 0%N U V hU hV T
  f endpoints.1 classes.1 (@current_homotopy_start_proper R h2 n nu 0%N A U V f g h geometry T hProper) psi.
have[betaK hK]:=@current_homotopy_test_replacement_exists R h2 n nu 0%N 0%N A U V f g h
  hHomotopy T hProper (@current_test_exterior_derivative R h2 nu 0%N V hV psi).
rewrite current_test_exterior_derivative_inclusion in hK.
exists betaG,betaF,betaK;split=>//;split=>//;split=>//.
exact:current_homotopy_zero_test_formula hG hF hK.
Qed.
End CurrentHomotopyZeroTestFormula.
