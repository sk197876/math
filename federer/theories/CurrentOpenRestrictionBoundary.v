(** Federer (1969), 4.1.7, pp. 357–359:
    the actual boundary commutes with restriction
    to an open subset. This supporting
    locality law uses original zero extension,
    genuine differentials and compact test support. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import CurrentEvaluation Hom RealNormUP NormMetric NormDifferentialUP NormDifferentialLocal
  NormDifferentialDirectional InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  AlternatingForms CurrentCoefficientNorms CurrentSpaces CurrentTestExteriorDerivative CurrentBoundary
  CurrentBoundarySupport CurrentSupportGeometry CurrentOpenRestriction
  ExteriorDerivativeUP ExteriorDifferentialUP SmoothFunctionSpaceUP SmoothFunctionSupport
  SmoothTestSpaces SmoothTestEvaluation TestZeroExtensionUP TestZeroExtensionSealed TestZeroExtensionLaws.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section CurrentOpenRestrictionBoundary.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n m:nat.
Local Notation X := (R_n R n).
Local Notation NX := (inner_norm (@euclidean_inner_productP R n)).
Local Notation hNX := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation Y := (fun k=>A_m X R^o k).
Local Notation NY := (fun k=>@current_form_comass R h2 n k).
Local Notation hNY := (fun k=>@current_form_comass_real_norm R h2 n k).
Variables U V:set X.
Hypothesis hU:forall x,U x->norm_domain_interior NX U x.
Arguments hU : clear implicits.
Hypothesis hV:forall x,V x->norm_domain_interior NX V x.
Arguments hV : clear implicits.
Hypothesis hUV:U `<=` V.
Local Notation A := (fun k=>@current_smooth_space R h2 n U hU k).
Local Notation B := (fun k=>@current_smooth_space R h2 n V hV k).
Local Notation av := (fun k=>@current_smooth_value R h2 n U hU k).
Local Notation bv := (fun k=>@current_smooth_value R h2 n V hV k).
Local Notation hA := (fun k=>@current_smooth_space_laws R h2 n U hU k).
Local Notation hB := (fun k=>@current_smooth_space_laws R h2 n V hV k).
Local Notation valueA := (fun k=>@current_test_value R h2 n U hU k).
Local Notation valueB := (fun k=>@current_test_value R h2 n V hV k).
Local Notation P := (fun k=>@current_open_test_extension R h2 n k U V hU hV hUV).
Local Notation dA := (@current_test_exterior_derivative R h2 n m U hU).
Local Notation dB := (@current_test_exterior_derivative R h2 n m V hV).

(** Source for [current_open_test_extension_support]:
    actual zero extension preserves the original
    support, supporting open restriction in Federer
    4.1.7, pp. 357–359, by 4.1.1,
    p. 345. *)
Theorem current_open_test_extension_support k psi:
  @current_test_support R h2 n k V hV (P k psi)=
    @current_test_support R h2 n k U hU psi.
Proof.
exact:(@test_zero_extension_support R X (Y k) NX (NY k) hNX (hNY k)
  U V hUV (A k) (B k) (av k) (bv k) (hA k) (hB k) (P k)
  (@TestZeroExtension.laws R X (Y k) NX (NY k) hNX (hNY k)
    U V hV hUV (A k) (B k) (av k) (bv k) (hA k) (hB k)) psi).
Qed.

(** Source for [current_open_test_exterior_commutes]:
    the actual exterior differential commutes
    with original test zero extension, supporting
    the boundary restriction in Federer 4.1.7,
    pp. 357–359. *)
Theorem current_open_test_exterior_commutes psi:P m.+1 (dA psi)=dB (P m psi).
Proof.
apply:(smooth_test_values_extensional (hB m.+1))=>x hxV.
change (valueB m.+1 (P m.+1 (dA psi)) x=valueB m.+1 (dB (P m psi)) x).
have hExtended:=@current_open_test_extension_values R h2 n m.+1 U V hU hV hUV (dA psi) x.
change (valueB m.+1 (P m.+1 (dA psi)) x=valueA m.+1 (dA psi) x) in hExtended.
apply:(eq_trans hExtended).
case:(pselect (U x))=>hxU.
- have [L [hL hExteriorA]]:=@current_test_exterior_derivative_actual R h2 n m U hU psi x hxU.
  have [M [hM hExteriorB]]:=@current_test_exterior_derivative_actual R h2 n m V hV (P m psi) x hxV.
  have hRestricted:=norm_differential_restrict hUV (hU x hxU) hM.
  have hOriginal:has_norm_differential NX (NY m) U (valueA m psi) x M.
    apply:(norm_differential_domain_agreement hNX _ hRestricted)=>y hy.
    exact:current_open_test_extension_values.
  have hSame:=norm_differential_unique hNX (hNY m) hL hOriginal.
  rewrite hSame in hExteriorA.
  exact:exterior_differential_value_unique hExteriorA hExteriorB.
- have hOutside:valueA m.+1 (dA psi) x=0:=
    @smooth_test_value_outside R X (Y m.+1) NX (NY m.+1) hNX (hNY m.+1)
      U (A m.+1) (av m.+1) (hA m.+1) (dA psi) x hxU.
  rewrite hOutside.
  apply:esym;case:(pselect (valueB m.+1 (dB (P m psi)) x=0))=>// hNonzero.
  have hSupport:@current_test_support R h2 n m.+1 V hV (dB (P m psi)) x.
    split;first exact:hxV.
    exact:(@subset_closure (real_norm_metric_space hNX) _ x hNonzero).
  have hOriginal:=@current_test_exterior_support_subset R h2 n m V hV (P m psi) x hSupport.
  rewrite current_open_test_extension_support in hOriginal.
  exact:False_ind _ (hxU hOriginal.1).
Qed.

(** Source for [current_open_restriction_boundary]:
    restriction to an open set commutes
    with the actual boundary, supporting the
    original local arguments and half-line example
    of Federer 4.1.7, pp. 357–359. *)
Theorem current_open_restriction_boundary (T:@current_space R h2 n V hV m.+1):
  @current_open_restriction R h2 n m U V hU hV hUV
    (@current_boundary R h2 n m V hV T)=
  @current_boundary R h2 n m U hU
    (@current_open_restriction R h2 n m.+1 U V hU hV hUV T).
Proof.
apply:(@current_values_extensional R h2 n m U hU)=>psi.
rewrite current_open_restriction_evaluation !current_boundary_evaluation
  current_open_restriction_evaluation.
by rewrite current_open_test_exterior_commutes.
Qed.
End CurrentOpenRestrictionBoundary.
