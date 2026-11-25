(** Federer (1969), 4.1.9, p. 363: the degree-zero
    homotopy formula for differential forms. Follow the printed
    proof by applying the current formula to every original
    point multivector current. Compact-current extensions justify
    the smooth-form evaluations; no homotopy properness is added
    to this pointwise assertion. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import Hom Bilinear RealNormUP NormDifferentialUP NormRegularity InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct ExteriorGrading ExteriorPowers AlternatingForms AlternatingPairing
  CurrentSpaces SmoothFunctionSpaceUP SmoothFunctionSpaceLaws SmoothFormPullbackSealed SmoothCurrentExteriorDerivative
  CurrentCompactSmoothValue PointMultivectorCurrentSealed PointMultivectorCurrentSupport PointMultivectorCurrentSmooth
  CurrentHomotopyUP CurrentHomotopyGeometry CurrentHomotopySliceClass CurrentHomotopyCompactCylinder
  CurrentHomotopyZeroSmoothFormula CurrentHomotopyTransgressionSealed CurrentHomotopyPointSupportAction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section CurrentHomotopyZeroFormFormula.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n nu:nat.
Local Notation X := (R_n R n).
Local Notation Y := (R_n R nu).
Local Notation Z := (R_n R (1+n)%N).
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
Local Notation ev := (@current_smooth_value R h2 n U hU 0%N).
Local Notation hEU := (@current_smooth_space_laws R h2 n U hU 0%N).
Local Notation PullF := (@SmoothFormPullback.operator R h2 n nu 0%N U V hU hV f endpoints.1 classes.1).
Local Notation PullG := (@SmoothFormPullback.operator R h2 n nu 0%N U V hU hV g endpoints.2 classes.2).
Local Notation d := (@smooth_current_exterior_derivative R h2 nu 0%N V hV).
Local Notation K := (@CurrentHomotopyTransgression.value R h2 n nu 0%N A U V f g h hHomotopy).

(** Source for [current_homotopy_zero_form_formula]: the
    original g#psi-f#psi equals the time integral of
    h#(d psi) in degree zero, Federer 4.1.9, p. 363.
    The actual smooth-form identity includes every original
    compact test form and has no negative-degree summand. *)
Theorem current_homotopy_zero_form_formula (psi:EV):
  (PullG psi-PullF psi:EU)=K (d psi).
Proof.
apply:(smooth_function_extensional hEU)=>x hx;apply:pairing_ext=>eta.
pose T:=@PointMultivectorCurrent.value R h2 n 0%N U hU x hx eta.
pose hT:=@point_multivector_current_compact R h2 n 0%N U hU x hx eta.
pose hPoint:=@point_multivector_current_support R h2 n 0%N U hU x hx eta.
pose hp:=@current_homotopy_compact_support_proper R h2 n nu 0%N A U V f g h hHomotopy T hT.
have hFormula:=@current_homotopy_zero_smooth_formula R h2 n nu A U V f g h hHomotopy T hp hT psi.
have hChain:=@current_deformation_chain_point_support_smooth_action R h2 n nu 0%N
  A U V f g h hHomotopy x hx T hPoint hT hp (d psi).
rewrite hChain in hFormula.
rewrite (@point_multivector_current_smooth_value R h2 n 0%N U hU x hx eta (PullG psi))
  (@point_multivector_current_smooth_value R h2 n 0%N U hU x hx eta (PullF psi))
  (@point_multivector_current_smooth_value R h2 n 0%N U hU x hx eta (K (d psi))) in hFormula.
have hDifference:ev (PullG psi-PullF psi) x=ev (PullG psi) x-ev (PullF psi) x.
  exact:(congr1 (fun k:X->A_m X R^o 0%N=>k x)
    (linearB (smooth_function_values_hom hEU) (PullG psi) (PullF psi))).
rewrite hDifference (linB ((@pairing_bilinear R X R^o 0%N).2 eta)).
exact:hFormula.
Qed.
End CurrentHomotopyZeroFormFormula.
