(** Federer (1969), 4.1.6, pp. 353–355:
    elementary calculus in the original induced norms
    for real differential forms. Constant forms are
    closed, and products of closed forms are closed,
    using the already proved original Leibniz rule. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions reals.
From Federer Require Import Hom Bilinear RealNormUP NormDifferentialUP NormDifferentialLinear
  InnerNorm HilbertFormCompactness EuclideanInnerProduct GrassmannAbbreviations
  Alternating AlternatingProduct ScalarCoefficients EuclideanFormNorm
  AlternatingFormNormUP ExteriorDifferentialUP ExteriorDifferentialSealed
  ExteriorDerivativeUP ExteriorDerivativeCoordinates ExteriorDerivativeLeibniz.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [real_euclidean_form_norm]: the original
    induced norm on real forms, Federer 4.1.6,
    p. 352, using the usual scalar absolute value. *)
Definition real_euclidean_form_norm (R:realType) (h2:(1+1:R)!=0) n m:
    A_m (R_n R n) R^o m->R:=
  @euclidean_form_norm R h2 n R^o (fun c:R^o=>`|c|) (@scalar_absolute_value_norm R) m.

(** Source for [real_euclidean_form_norm_laws]: its
    exact original multilinear bound,
    Federer 4.1.6, p. 352. *)
Lemma real_euclidean_form_norm_laws (R:realType) (h2:(1+1:R)!=0) n m:
  is_alternating_form_norm (inner_norm (@euclidean_inner_productP R n)) (fun c:R^o=>`|c|)
    (@real_euclidean_form_norm R h2 n m).
Proof. exact:euclidean_form_norm_laws. Qed.

(** Source for [real_euclidean_form_norm_norm]: the
    induced norm is a genuine norm,
    Federer 4.1.6, p. 352, in every degree. *)
Lemma real_euclidean_form_norm_norm (R:realType) (h2:(1+1:R)!=0) n m:
  is_real_norm (@real_euclidean_form_norm R h2 n m).
Proof. exact:euclidean_form_norm_real_norm. Qed.

(** Source for [has_real_form_derivative]: the original
    derivative on the actual induced real form norm,
    Federer 4.1.6, pp. 352–353. *)
Definition has_real_form_derivative (R:realType) (h2:(1+1:R)!=0) n m
    (U:R_n R n->Prop) (phi:R_n R n->A_m (R_n R n) R^o m) a b:Prop:=
  has_exterior_derivative (inner_norm (@euclidean_inner_productP R n))
    (@real_euclidean_form_norm R h2 n m) U phi a b.

(** Source for [constant_real_form_closed]: the actual
    first differential of a constant form is zero,
    supporting the coordinate generators in
    Federer 4.1.6, pp. 353–355. *)
Theorem constant_real_form_closed (R:realType) (h2:(1+1:R)!=0) n m
    (U:R_n R n->Prop) a (c:A_m (R_n R n) R^o m):
  norm_domain_interior (inner_norm (@euclidean_inner_productP R n)) U a->
  has_real_form_derivative h2 U (fun _=>c) a 0.
Proof.
move=>hInterior; exists 0; split.
- exact:(@norm_differential_constant R (R_n R n) (A_m (R_n R n) R^o m)
    (inner_norm (@euclidean_inner_productP R n)) (@real_euclidean_form_norm R h2 n m)
    (inner_norm_real_norm (@euclidean_inner_productP R n))
    (@real_euclidean_form_norm_norm R h2 n m) U a c hInterior).
- have hZero:=lin0 (@exterior_differential_linear R h2 n R^o m).
  rewrite -hZero; exact:ExteriorDifferential.laws.
Qed.

(** Source for [closed_real_forms_product_closed]: the
    original graded Leibniz rule makes the product
    of two closed forms closed,
    Federer 4.1.6, pp. 353–355. *)
Theorem closed_real_forms_product_closed (R:realType) (h2:(1+1:R)!=0) n p q
    (U:R_n R n->Prop) (phi:R_n R n->A_m (R_n R n) R^o p)
    (psi:R_n R n->A_m (R_n R n) R^o q) a:
  has_real_form_derivative h2 U phi a 0->has_real_form_derivative h2 U psi a 0->
  has_real_form_derivative h2 U (fun x=>form_wedge h2 (scalar_bilinear R) (phi x) (psi x)) a 0.
Proof.
move=>hPhi hPsi.
have [d [hd he]]:=@exterior_derivative_leibniz R h2 n p q
  (@real_euclidean_form_norm R h2 n p) (@real_euclidean_form_norm R h2 n q)
  (@real_euclidean_form_norm R h2 n (p+q))
  (@real_euclidean_form_norm_norm R h2 n p) (@real_euclidean_form_norm_norm R h2 n q)
  (@real_euclidean_form_norm_norm R h2 n (p+q))
  (@real_euclidean_form_norm_laws R h2 n p) (@real_euclidean_form_norm_laws R h2 n q)
  (@real_euclidean_form_norm_laws R h2 n (p+q)) U phi psi a 0 0 hPhi hPsi.
have hZero:d=0.
  apply:(can_inj (@form_includeK R (R_n R n) R^o (p+q).+1)).
  rewrite he !linear0 (bil0l (@alternating_wedge_bilinear R h2 (R_n R n) R^o _ (scalar_bilinear R)))
    (bil0r (@alternating_wedge_bilinear R h2 (R_n R n) R^o _ (scalar_bilinear R))) scaler0 addr0.
  by [].
by rewrite -hZero.
Qed.
