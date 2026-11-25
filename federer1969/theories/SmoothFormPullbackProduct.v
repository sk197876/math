(** Federer (1969), 4.1.7, p. 359:
    pullback preserves the original smooth
    alternating product. This actual-space law
    is the direct consequence of
    1.4.2, p. 18, used in
    the projection formula for currents. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals.
From Federer Require Import Hom RealNormUP NormDifferentialUP NormClassOneUP NormRegularity
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct AlternatingForms
  AlternatingProduct ScalarCoefficients FormPullbackProduct CurrentSpaces
  SmoothFunctionSpaceLaws SmoothFormPullbackUP SmoothFormPullbackSealed SmoothCurrentFormProduct.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Section SmoothFormPullbackProduct.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables v n k p:nat.
Local Notation X := (R_n R v).
Local Notation Y := (R_n R n).
Local Notation NX := (inner_norm (@euclidean_inner_productP R v)).
Local Notation NY := (inner_norm (@euclidean_inner_productP R n)).
Local Notation hNX := (inner_norm_real_norm (@euclidean_inner_productP R v)).
Local Notation hNY := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Variables (U:X->Prop) (V:Y->Prop).
Hypothesis hU:forall x,U x->norm_domain_interior NX U x.
Arguments hU : clear implicits.
Hypothesis hV:forall y,V y->norm_domain_interior NY V y.
Arguments hV : clear implicits.
Local Notation E := (fun d=>@current_smooth_space R h2 n V hV d).
Local Notation F := (fun d=>@current_smooth_space R h2 v U hU d).
Local Notation ev := (fun d=>@current_smooth_value R h2 n V hV d).
Local Notation fv := (fun d=>@current_smooth_value R h2 v U hU d).
Variable f:X->Y.
Hypothesis hImage:forall x,U x->V (f x).
Arguments hImage : clear implicits.
Hypothesis hf:norm_class_all_orders hNX hNY U f.
Local Notation pull := (fun d=>@SmoothFormPullback.operator R h2 v n d U V hU hV f hImage hf).
Local Notation productU := (@smooth_current_form_product R h2 v k p U hU).
Local Notation productV := (@smooth_current_form_product R h2 n k p V hV).

(** Source for [smooth_form_pullback_product]:
    f#(phi wedge psi)=f#phi wedge f#psi
    in the actual original smooth
    spaces, supporting the projection formula
    in Federer 4.1.7, p. 359.
    Every pair of original nonnegative
    degrees is retained. *)
Theorem smooth_form_pullback_product (phi:E k) (psi:E p):
  pull (k+p) (productV phi psi)=productU (pull k phi) (pull p psi).
Proof.
apply:(smooth_function_extensional (@current_smooth_space_laws R h2 v U hU (k+p)))=>x hx.
have [D hD]:=(@norm_class_firstP R X Y NX NY hNX hNY U f).1 (hf 1%N).
have hActual:=norm_class_one_differential hD hx.
have hLeft:=@smooth_form_pullback_values R v n (k+p) U V (E (k+p)) (F (k+p))
  (ev (k+p)) (fv (k+p)) f (pull (k+p))
  (@SmoothFormPullback.laws R h2 v n (k+p) U V hU hV f hImage hf)
  (productV phi psi) x (D x) hx hActual.
rewrite (@smooth_current_form_product_values R h2 n k p V hV phi psi (f x) (hImage x hx))
  form_pullback_product in hLeft.
have hRight:=@smooth_current_form_product_values R h2 v k p U hU (pull k phi) (pull p psi) x hx.
rewrite (@smooth_form_pullback_values R v n k U V (E k) (F k) (ev k) (fv k) f (pull k)
  (@SmoothFormPullback.laws R h2 v n k U V hU hV f hImage hf) phi x (D x) hx hActual)
  (@smooth_form_pullback_values R v n p U V (E p) (F p) (ev p) (fv p) f (pull p)
  (@SmoothFormPullback.laws R h2 v n p U V hU hV f hImage hf) psi x (D x) hx hActual) in hRight.
exact:(eq_trans hLeft (esym hRight)).
Qed.
End SmoothFormPullbackProduct.
