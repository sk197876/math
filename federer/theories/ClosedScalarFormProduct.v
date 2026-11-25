(** Federer (1969), 4.1.6, p. 355: multiply
    a closed coordinate product by a differentiable
    scalar coefficient. The original Leibniz rule
    leaves exactly the coefficient differential term. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions reals.
From Federer Require Import Hom Bilinear RealNormUP NormDifferentialUP
  InnerNorm HilbertFormCompactness EuclideanInnerProduct GrassmannAbbreviations
  Alternating AlternatingProduct OneFormIdentification ScalarCoefficients
  ExteriorDerivativeUP ExteriorDerivativeLeibniz ExteriorDerivativeZeroDegree
  RealDifferentialFormCalculus ZeroFormScalarProduct.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [real_closed_form_scalar_product_derivative]:
    d(c wedge psi)=dc wedge psi when d psi=0,
    the coefficient step in the original generator
    argument of Federer 4.1.6, p. 355. *)
Theorem real_closed_form_scalar_product_derivative (R:realType) (h2:(1+1:R)!=0) n m
    (U:R_n R n->Prop) (c:R_n R n->R^o) (psi:R_n R n->A_m (R_n R n) R^o m)
    a (L:Hom (R_n R n) R^o):
  has_norm_differential (inner_norm (@euclidean_inner_productP R n)) (fun t:R^o=>`|t|) U c a L->
  has_real_form_derivative h2 U psi a 0->
  exists d:A_m (R_n R n) R^o m.+1,
    has_real_form_derivative h2 U (fun x=>c x*:psi x) a d /\
    form_include d=alternating_wedge h2 (scalar_bilinear R) (form_include (one_form L)) (form_include (psi a)).
Proof.
move=>hC hPsi.
have hScalar:=@exterior_derivative_zero_degree R (R_n R n) R^o
  (inner_norm (@euclidean_inner_productP R n)) (fun t:R^o=>`|t|)
  (inner_norm_real_norm (@euclidean_inner_productP R n)) (@scalar_absolute_value_norm R)
  (@real_euclidean_form_norm R h2 n 0) (@real_euclidean_form_norm_laws R h2 n 0) U c a L hC.
have [d [hd he]]:=@exterior_derivative_leibniz R h2 n 0 m
  (@real_euclidean_form_norm R h2 n 0) (@real_euclidean_form_norm R h2 n m)
  (@real_euclidean_form_norm R h2 n m)
  (@real_euclidean_form_norm_norm R h2 n 0) (@real_euclidean_form_norm_norm R h2 n m)
  (@real_euclidean_form_norm_norm R h2 n m)
  (@real_euclidean_form_norm_laws R h2 n 0) (@real_euclidean_form_norm_laws R h2 n m)
  (@real_euclidean_form_norm_laws R h2 n m) U
  (fun x=>@zero_form R (R_n R n) R^o (c x)) psi a (one_form L) 0 hScalar hPsi.
have hFunction:(fun x=>form_wedge h2 (scalar_bilinear R) (@zero_form R (R_n R n) R^o (c x)) (psi x))=
    (fun x=>c x*:psi x).
  apply:funext=>x; exact:original_zero_form_wedge_scalar.
rewrite hFunction in hd.
exists d; split; first exact:hd.
rewrite expr0 scale1r linear0
  (bil0r (@alternating_wedge_bilinear R h2 (R_n R n) R^o _ (scalar_bilinear R))) addr0 in he.
exact:he.
Qed.
