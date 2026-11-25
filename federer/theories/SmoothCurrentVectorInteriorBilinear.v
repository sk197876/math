(** Federer (1969), 4.1.8, p. 360: the original
    first-variable slice is linear in eta and phi. This
    supporting law applies the pointwise interior from 4.1.7,
    pp. 355–356, to the actual smooth field spaces. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals.
From Federer Require Import Hom TensorUP Bilinear RealNormUP NormDifferentialUP
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  ExteriorGrading AlternatingForms CurrentCoefficientNorms CurrentSpaces
  CurrentVectorSpaces CurrentVectorFormInterior SmoothCurrentVectorInterior
  SmoothFunctionSpaceUP SmoothFunctionSpaceLaws.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section SmoothCurrentVectorInteriorBilinear.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n k p:nat.
Local Notation X := (R_n R n).
Local Notation NX := (inner_norm (@euclidean_inner_productP R n)).
Local Notation hNX := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation Y := (fun d=>A_m X R^o d).
Local Notation Z := (fun d=>exterior_power X d).
Local Notation NY := (fun d=>@current_form_comass R h2 n d).
Local Notation hNY := (fun d=>@current_form_comass_real_norm R h2 n d).
Local Notation NZ := (fun d=>@current_vector_mass R h2 n d).
Local Notation hNZ := (fun d=>@current_vector_mass_real_norm R h2 n d).
Variable U:set X.
Hypothesis hU:forall x,U x->norm_domain_interior NX U x.
Local Notation E := (fun d=>@current_smooth_space R h2 n U hU d).
Local Notation ev := (fun d=>@current_smooth_value R h2 n U hU d).
Local Notation hE := (fun d=>@current_smooth_space_laws R h2 n U hU d).
Local Notation V := (fun d=>@current_vector_smooth_space R h2 n U hU d).
Local Notation vv := (fun d=>@current_vector_smooth_value R h2 n U hU d).
Local Notation hV := (fun d=>@current_vector_smooth_space_laws R h2 n U hU d).
Local Notation P := (@smooth_current_vector_interior R h2 n k p U hU).
Local Notation B := (@current_vector_form_interior R X k p).

(** Source for [smooth_current_vector_interior_bilinear]: the
    actual smooth interior is linear in both the vector
    and the form, supporting the slice definition in Federer
    4.1.8, p. 360. Every nonnegative degree is retained. *)
Theorem smooth_current_vector_interior_bilinear:
  bilinear (fun xi phi=>P xi phi).
Proof.
split.
- move=>phi c xi eta.
  apply:(smooth_function_extensional (hE p))=>x hx.
  have hInput:=@smooth_function_evaluation_linear R X (Z k) NX (NZ k) hNX (hNZ k)
    U (V k) (vv k) (hV k) c xi eta x.
  have hOutput:=@smooth_function_evaluation_linear R X (Y p) NX (NY p) hNX (hNY p)
    U (E p) (ev p) (hE p) c (P xi phi) (P eta phi) x.
  have hSum:=@smooth_current_vector_interior_values R h2 n k p U hU (c*:xi+eta) phi x hx.
  have hXi:=@smooth_current_vector_interior_values R h2 n k p U hU xi phi x hx.
  have hEta:=@smooth_current_vector_interior_values R h2 n k p U hU eta phi x hx.
  have hCoefficient:=(@current_vector_form_interior_bilinear R X k p).1
    (ev (k+p) phi x) c (vv k xi x) (vv k eta x).
  exact:(eq_trans hSum (eq_trans
    (congr1 (fun a:Z k=>B a (ev (k+p) phi x)) hInput)
    (eq_trans hCoefficient (eq_trans
      (congr2 (fun a b:Y p=>c*:a+b) (esym hXi) (esym hEta))
      (esym hOutput))))).
- move=>xi;exact:(hom_linear (P xi)).
Qed.
End SmoothCurrentVectorInteriorBilinear.
