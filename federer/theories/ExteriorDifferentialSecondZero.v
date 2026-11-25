(** Federer (1969), 4.1.6, p. 353: the
    symmetric second differential cancels against the
    original antisymmetric pair of coordinate covectors.
    This algebraic cancellation precedes the analytic
    d(d phi)=0 theorem. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions reals.
From Federer Require Import Hom Bilinear Exterior Alternating ScalarTensorContraction
  GrassmannAbbreviations FiniteCoordinates EuclideanCoordinateForms
  MixedAlternatingProduct MixedScalarOneProductsSkew
  ExteriorDifferentialSealed ExteriorDerivativeCoordinates.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [finite_skew_double_sum_zero]: the final
    cancellation of the two coordinate sums in
    Federer 4.1.6, p. 353. The diagonal
    terms are covered by the same identity. *)
Lemma finite_skew_double_sum_zero (K:fieldType) (h2:(1+1:K)!=0)
    (I:finType) (W:lmodType K) (f:I->I->W):
  (forall i j,f i j= -f j i)->\sum_i \sum_j f i j=0.
Proof.
move=>hSkew; pose s:=\sum_i \sum_j f i j.
have hN:s= -s.
  rewrite /s.
  transitivity (\sum_(i:I) \sum_(j:I) -f j i).
  - apply:eq_bigr=>i _; apply:eq_bigr=>j _; exact:(hSkew i j).
  - under [LHS]eq_bigr do rewrite sumrN.
    by rewrite sumrN exchange_big.
have hZero:(1+1:K)*:s=0.
  by rewrite scalerDl !scale1r {1}hN addNr.
move/eqP:hZero; by rewrite scaler_eq0 (negbTE h2) orFb=>/eqP.
Qed.

(** Source for [exterior_differential_symmetric_second_zero]:
    the original symmetric bilinear second differential
    maps to zero under two exterior alternations,
    Federer 4.1.6, p. 353. Arbitrary
    coefficient spaces and degree zero remain included. *)
Theorem exterior_differential_symmetric_second_zero (R:realType) (h2:(1+1:R)!=0)
    n (W:lmodType R) m
    (B:Hom (R_n R n) (Hom (R_n R n) (A_m (R_n R n) W m))):
  (forall u v,B u v=B v u)->
  @ExteriorDifferential.value R h2 n W m.+1
    (hom_comp (@exterior_differential_map R h2 n W m) B)=0.
Proof.
move=>hSym; rewrite exterior_differential_coordinate_formula.
have hTerm (k:'I_n):
  mixed_form_product h2 (@scalar_action_bilinear R W) (euclidean_coordinate_form k)
    (hom_comp (@exterior_differential_map R h2 n W m) B (@coordinate_basis R n k))=
  \sum_(j:'I_n) mixed_form_product h2 (@scalar_action_bilinear R W) (euclidean_coordinate_form k)
    (mixed_form_product h2 (@scalar_action_bilinear R W) (euclidean_coordinate_form j)
      (B (@coordinate_basis R n k) (@coordinate_basis R n j))).
  rewrite hom_compE /exterior_differential_map /= exterior_differential_coordinate_formula.
  exact:(big_morph (mixed_form_product h2 (@scalar_action_bilinear R W) (euclidean_coordinate_form k))
    (bilDr (@mixed_form_product_bilinear R h2 (R_n R n) R^o W W _ (@scalar_action_bilinear R W) 1 m.+1)
      (euclidean_coordinate_form k))
    (bil0r (@mixed_form_product_bilinear R h2 (R_n R n) R^o W W _ (@scalar_action_bilinear R W) 1 m.+1)
      (euclidean_coordinate_form k)) _ _ _).
under eq_bigr do rewrite hTerm.
apply:(finite_skew_double_sum_zero h2)=>k j.
rewrite hSym; exact:mixed_scalar_one_products_skew.
Qed.
