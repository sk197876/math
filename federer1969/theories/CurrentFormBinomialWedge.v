(** Federer (1969), 4.1.8, p. 361: the original
    covector binomial estimate follows from the already
    proved alternating-product bound of 4.1.6. The actual
    comass and scalar norm retain both zero degrees. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import Hom TensorUP ScalarCoefficients RealNormUP InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct AlternatingForms AlternatingProduct
  CurrentCoefficientNorms CurrentFormInducedNorm MixedAlternatingProductNorm MixedOrdinaryFormProduct.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [current_comass_binomial_wedge]: the
    original covector product has the binomial comass bound,
    supporting Federer 4.1.8, p. 361, by 1.8.1, p. 39.
    Every natural pair of degrees is retained. *)
Theorem current_comass_binomial_wedge (R:realType) (h2:(1+1:R)!=0) n i j
    (phi:A_m (R_n R n) R^o i) (psi:A_m (R_n R n) R^o j):
  @current_form_comass R h2 n (i+j) (form_wedge h2 (scalar_bilinear R) phi psi)<=
    'C(i+j,i)%:R*(@current_form_comass R h2 n i phi*@current_form_comass R h2 n j psi).
Proof.
have hScalar:forall u v:R^o,`|u*v|<=1*(`|u|*`|v|) by move=>u v;rewrite normrM mul1r.
have h:=@mixed_alternating_product_norm_bound R h2 (R_n R n) R^o R^o R^o
  (@euclidean_inner_product R n) (@euclidean_inner_productP R n)
  (fun a:R^o=>`|a|) (fun a:R^o=>`|a|) (fun a:R^o=>`|a|)
  (@scalar_absolute_value_norm R) (@scalar_absolute_value_norm R) (@scalar_absolute_value_norm R)
  (fun a b:R^o=>a*b) (@scalar_bilinear R) 1 (@ler01 R) hScalar i j
  (@current_form_comass R h2 n i) (@current_form_comass R h2 n j)
  (@current_form_comass R h2 n (i+j))
  (@current_form_comass_is_induced R h2 n i) (@current_form_comass_is_induced R h2 n j)
  (@current_form_comass_is_induced R h2 n (i+j)) phi psi.
by rewrite mixed_same_form_product mulr1 in h.
Qed.
