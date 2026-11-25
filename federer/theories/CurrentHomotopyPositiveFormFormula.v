(** Federer (1969), 4.1.9, p. 363: the positive-degree
    homotopy formula for differential forms. Follow the printed
    proof by applying the current formula to every original
    point multivector current. Compact-current extensions justify
    the smooth-form evaluations; no homotopy properness is added
    to this pointwise assertion. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import Hom Bilinear RealNormUP NormDifferentialUP NormRegularity InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct ExteriorGrading ExteriorPowers AlternatingForms AlternatingPairing
  CurrentSpaces SmoothFunctionSpaceUP SmoothFunctionSpaceLaws SmoothFormPullbackSealed SmoothCurrentExteriorDerivative
  CurrentBoundary CurrentBoundarySupport CurrentCompactBoundarySmooth CurrentCompactSmoothValue PointMultivectorCurrentSealed PointMultivectorCurrentSupport PointMultivectorCurrentSmooth
  CurrentHomotopyUP CurrentHomotopyGeometry CurrentHomotopySliceClass CurrentHomotopyCompactCylinder
  CurrentHomotopyPositiveSmoothFormula CurrentHomotopyBoundaryCylinder CurrentHomotopyTransgressionSealed CurrentHomotopyPointSupportAction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section CurrentHomotopyPositiveFormFormula.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n nu j:nat.
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
Local Notation EU := (@current_smooth_space R h2 n U hU j.+1).
Local Notation EV := (@current_smooth_space R h2 nu V hV j.+1).
Local Notation ev := (@current_smooth_value R h2 n U hU j.+1).
Local Notation hEU := (@current_smooth_space_laws R h2 n U hU j.+1).
Local Notation PullF := (@SmoothFormPullback.operator R h2 n nu j.+1 U V hU hV f endpoints.1 classes.1).
Local Notation PullG := (@SmoothFormPullback.operator R h2 n nu j.+1 U V hU hV g endpoints.2 classes.2).
Local Notation d := (@smooth_current_exterior_derivative R h2 nu j.+1 V hV).
Local Notation K := (@CurrentHomotopyTransgression.value R h2 n nu j.+1 A U V f g h hHomotopy).
Local Notation KLower := (@CurrentHomotopyTransgression.value R h2 n nu j A U V f g h hHomotopy).
Local Notation dU := (@smooth_current_exterior_derivative R h2 n j U hU).


(** Source for [current_homotopy_positive_form_formula]:
    the original positive-degree identity is g#psi-f#psi
    equals K(d psi)+d(K psi), Federer 4.1.9, p. 363.
    Both operators are the actual smooth homotopy integrals;
    no support or properness hypothesis on the homotopy is added. *)
Theorem current_homotopy_positive_form_formula (psi:EV):
  (PullG psi-PullF psi:EU)=K (d psi)+dU (KLower psi).
Proof.
apply:(smooth_function_extensional hEU)=>x hx;apply:pairing_ext=>eta.
pose T:=@PointMultivectorCurrent.value R h2 n j.+1 U hU x hx eta.
pose hT:=@point_multivector_current_compact R h2 n j.+1 U hU x hx eta.
pose hPoint:=@point_multivector_current_support R h2 n j.+1 U hU x hx eta.
pose hp:=@current_homotopy_compact_support_proper R h2 n nu j.+1 A U V f g h hHomotopy T hT.
pose B:=@current_boundary R h2 n j U hU T.
pose hB:=@current_compact_boundary_compact R h2 n j U hU T hT.
have hPointB:forall y,@current_support R h2 n U hU j B y->[set x] y.
  move=>y hy;exact:(@hPoint y (@current_boundary_support_subset R h2 n j U hU T y hy)).
pose hpB:=@current_homotopy_boundary_cylinder_proper R h2 n nu j A U V f g h geometry T hp.
have hFormula:=@current_homotopy_positive_smooth_formula R h2 n nu j A U V f g h hHomotopy T hp hT psi.
have hChain:=@current_deformation_chain_point_support_smooth_action R h2 n nu j.+1
  A U V f g h hHomotopy x hx T hPoint hT hp (d psi).
have hBoundaryChain:=@current_deformation_chain_point_support_smooth_action R h2 n nu j
  A U V f g h hHomotopy x hx B hPointB hB hpB psi.
rewrite hChain hBoundaryChain
  (@current_compact_boundary_smooth_value R h2 n j U hU T hT (KLower psi)) in hFormula.
rewrite (@point_multivector_current_smooth_value R h2 n j.+1 U hU x hx eta (PullG psi))
  (@point_multivector_current_smooth_value R h2 n j.+1 U hU x hx eta (PullF psi))
  (@point_multivector_current_smooth_value R h2 n j.+1 U hU x hx eta (K (d psi)))
  (@point_multivector_current_smooth_value R h2 n j.+1 U hU x hx eta (dU (KLower psi))) in hFormula.
have hDifference:ev (PullG psi-PullF psi) x=ev (PullG psi) x-ev (PullF psi) x.
  exact:(congr1 (fun k:X->A_m X R^o j.+1=>k x)
    (linearB (smooth_function_values_hom hEU) (PullG psi) (PullF psi))).
have hSum:ev (K (d psi)+dU (KLower psi)) x=ev (K (d psi)) x+ev (dU (KLower psi)) x.
  exact:(congr1 (fun k:X->A_m X R^o j.+1=>k x)
    (linearD (smooth_function_values_hom hEU) (K (d psi)) (dU (KLower psi)))).
rewrite hDifference hSum (linB ((@pairing_bilinear R X R^o j.+1).2 eta))
  (linD ((@pairing_bilinear R X R^o j.+1).2 eta)).
exact:hFormula.
Qed.
End CurrentHomotopyPositiveFormFormula.
