(** Federer (1969), 4.1.8, p. 360: bilinearity of the separated
    tests follows from the original smooth alternating product.
    This supporting law uses the actual smooth-space pointwise laws
    of 4.1.6, p. 351, and the public multiplier from 4.1.7. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals.
From Federer Require Import Hom TensorUP Bilinear RealNormUP NormDifferentialUP
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  AlternatingForms AlternatingProduct ScalarCoefficients CurrentCoefficientNorms
  CurrentSpaces SmoothCurrentFormProduct SmoothFunctionSpaceUP SmoothFunctionSpaceLaws.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section SmoothCurrentFormProductBilinear.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n k l:nat.
Local Notation X := (R_n R n).
Local Notation NX := (inner_norm (@euclidean_inner_productP R n)).
Local Notation hNX := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation Y := (fun d=>A_m X R^o d).
Local Notation NY := (fun d=>@current_form_comass R h2 n d).
Local Notation hNY := (fun d=>@current_form_comass_real_norm R h2 n d).
Variable U:set X.
Hypothesis hU:forall x,U x->norm_domain_interior NX U x.
Local Notation E := (fun d=>@current_smooth_space R h2 n U hU d).
Local Notation ev := (fun d=>@current_smooth_value R h2 n U hU d).
Local Notation hE := (fun d=>@current_smooth_space_laws R h2 n U hU d).
Local Notation P := (@smooth_current_form_product R h2 n k l U hU).
Local Notation W := (@form_wedge R h2 X R^o (fun a b=>a*b) (@scalar_bilinear R) k l).

(** Source for [smooth_current_form_product_bilinear]: the product
    p#alpha wedge q#beta in Federer 4.1.8, p. 360 is linear in
    each smooth form. This supporting result concerns the actual
    smooth-space operators and retains every nonnegative degree. *)
Theorem smooth_current_form_product_bilinear:
  bilinear (fun phi psi=>P phi psi).
Proof.
split.
- move=>psi c phi chi.
  apply:(smooth_function_extensional (hE (k+l)))=>z hz.
  have hInput:=@smooth_function_evaluation_linear R X (Y k) NX (NY k) hNX (hNY k)
    U (E k) (ev k) (hE k) c phi chi z.
  have hOutput:=@smooth_function_evaluation_linear R X (Y (k+l)) NX (NY (k+l))
    hNX (hNY (k+l)) U (E (k+l)) (ev (k+l)) (hE (k+l))
    c (P phi psi) (P chi psi) z.
  have hSum:=@smooth_current_form_product_values R h2 n k l U hU
    (c*:phi+chi) psi z hz.
  have hPhi:=@smooth_current_form_product_values R h2 n k l U hU phi psi z hz.
  have hChi:=@smooth_current_form_product_values R h2 n k l U hU chi psi z hz.
  have [hWL _]:=@form_wedge_bilinear R h2 X R^o
    (fun a b=>a*b) (@scalar_bilinear R) k l.
  have hCoefficient:=@hWL (ev l psi z) c (ev k phi z) (ev k chi z).
  exact:(eq_trans hSum (eq_trans
    (congr1 (fun a:Y k=>W a (ev l psi z)) hInput)
    (eq_trans hCoefficient (eq_trans
      (congr2 (fun a b:Y (k+l)=>c*:a+b) (esym hPhi) (esym hChi))
      (esym hOutput))))).
- move=>phi;exact:(hom_linear (P phi)).
Qed.
End SmoothCurrentFormProductBilinear.
