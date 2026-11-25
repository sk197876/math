(** Federer (1969), 4.1.12, p. 367: multiplication
    by a scalar test and its differential uses
    the sharp constant-one wedge estimate of 1.8.1,
    p. 39. Reuse simplicity of a one-covector
    and the original opaque comass laws. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import Hom TensorUP Bilinear RealNormUP InnerNorm
  HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct FiniteCoordinates
  Alternating AlternatingForms AlternatingProduct AlternatingUnit ScalarCoefficients
  OneFormProducts OneFormProductHead SimpleCovectors ComassSimpleWedgeBound
  Comass CurrentCoefficientNorms CurrentFormBinomialWedge.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [current_one_covector_simple]: every
    one-covector is simple, by the original single-
    factor product definition in Federer 1.6.3,
    p. 24. This supports the sharp multiplier
    estimate in 4.1.12, p. 367. *)
Lemma current_one_covector_simple (K:fieldType) (h2:(1+1:K)!=0)
    (V:lmodType K) (alpha:A_m V K^o 1):simple_covector h2 alpha.
Proof.
exists (fun _:'I_1=>alpha).
apply:(can_inj (@form_includeK K V K^o 1)).
rewrite original_one_forms_wedge_head original_one_forms_wedge_empty.
rewrite (@form_wedge_include K h2 V K^o _ (scalar_bilinear K) 1 0 alpha (@zero_form K V K^o 1)).
exact:(esym (@alternating_unit_right K h2 V K^o (fun a b=>a*b)
  (scalar_bilinear K) 1 (@mulr1 K) (form_include alpha))).
Qed.

(** Source for [current_one_form_comass_wedge_bound]:
    wedging a one-covector with any covector has
    comass at most the product of their comasses,
    by Federer 1.8.1, p. 39, supporting the
    exact coefficient in 4.1.12, p. 367.
    The degree-zero second factor is included. *)
Theorem current_one_form_comass_wedge_bound (R:realType) (h2:(1+1:R)!=0) n m
    (alpha:A_m (R_n R n) R^o 1) (psi:A_m (R_n R n) R^o m):
  @current_form_comass R h2 n (1+m) (form_wedge h2 (scalar_bilinear R) alpha psi)<=
    @current_form_comass R h2 n 1 alpha * @current_form_comass R h2 n m psi.
Proof.
case:m psi=>[|q] psi.
- have h:=@current_comass_binomial_wedge R h2 n 1 0 alpha psi.
  by rewrite binn mul1r in h.
- apply:(@comass_simple_left_wedge_bound R h2 (R_n R n)
    (@euclidean_inner_product R n) (@euclidean_inner_productP R n)
    n (@coordinate_basis R n) (@coordinate_basisP R n) 1 q.+1
    (ltn0Sn 0) (ltn0Sn q) alpha psi
    (@current_form_comass R h2 n 1 alpha)
    (@current_form_comass R h2 n q.+1 psi)
    (@current_form_comass R h2 n (1+q.+1) (form_wedge h2 (scalar_bilinear R) alpha psi))).
  + exact:current_one_covector_simple.
  + exact:comassP.
  + exact:comassP.
  + exact:comassP.
Qed.
