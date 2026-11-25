(** Federer (1969), 4.1.12, p. 367: the
    scalar test product and its differential have
    the exact pointwise comass bounds used in the
    printed multiplier estimate. Reuse 1.8.1, p. 39,
    and the preceding actual Leibniz identity. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import Hom TensorUP Bilinear RealNormUP NormDifferentialUP InnerNorm
  HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct AlternatingForms
  AlternatingProduct ScalarCoefficients CurrentCoefficientNorms CurrentSpaces
  SmoothTestSpaces CurrentTestFormProduct CurrentTestExteriorDerivative
  SmoothCurrentExteriorDerivative CurrentFormBinomialWedge CurrentOneFormWedgeBound
  CurrentScalarProductDerivativeValues.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [current_zero_form_comass_wedge_bound]:
    a scalar covector multiplies the original comass
    with constant one, supporting the multiplier
    estimate of Federer 4.1.12, p. 367,
    by the zero-degree case of 1.8.1, p. 39. *)
Theorem current_zero_form_comass_wedge_bound (R:realType) (h2:(1+1:R)!=0) n m
    (gamma:A_m (R_n R n) R^o 0%N) (phi:A_m (R_n R n) R^o m):
  @current_form_comass R h2 n m (form_wedge h2 (scalar_bilinear R) gamma phi)<=
    @current_form_comass R h2 n 0%N gamma * @current_form_comass R h2 n m phi.
Proof.
have h:=@current_comass_binomial_wedge R h2 n 0%N m gamma phi.
by rewrite bin0 mul1r in h.
Qed.

Section CurrentScalarProductNorm.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n m:nat.
Local Notation X := (R_n R n).
Variable U:X->Prop.
Hypothesis hU:forall x,U x->norm_domain_interior
  (inner_norm (@euclidean_inner_productP R n)) U x.
Arguments hU : clear implicits.
Local Notation E k := (@current_smooth_space R h2 n U hU k).
Local Notation sv k := (@current_smooth_value R h2 n U hU k).
Local Notation DT k := (@current_test_space R h2 n U hU k).
Local Notation value k := (@current_test_value R h2 n U hU k).
Local Notation N k := (@current_form_comass R h2 n k).
Local Notation sd k := (@smooth_current_exterior_derivative R h2 n k U hU).
Local Notation td k := (@current_test_exterior_derivative R h2 n k U hU).
Local Notation product gamma := (@current_test_form_product R h2 n 0%N m U hU gamma).

(** Source for [current_scalar_test_product_comass_bound]:
    the original product gamma wedge phi has
    pointwise comass at most the product of the
    two comasses, supporting Federer 4.1.12, p. 367. *)
Lemma current_scalar_test_product_comass_bound (gamma:E 0%N) (phi:DT m) x:
  U x->N m (value m (product gamma phi) x)<=N 0%N (sv 0%N gamma x) * N m (value m phi x).
Proof.
move=>hx;rewrite (@current_test_form_product_values R h2 n 0%N m U hU gamma phi x hx).
exact:current_zero_form_comass_wedge_bound.
Qed.

(** Source for [current_scalar_test_derivative_comass_bound]:
    the comass of d(gamma wedge phi) is at most
    the sum of the two printed Leibniz products,
    supporting the exact coefficient in Federer
    4.1.12, p. 367. No binomial loss is used. *)
Lemma current_scalar_test_derivative_comass_bound (gamma:E 0%N) (phi:DT m) x:
  U x->N m.+1 (value m.+1 (td m (product gamma phi)) x)<=
    N 1%N (sv 1%N (sd 0%N gamma) x) * N m (value m phi x)+
    N 0%N (sv 0%N gamma x) * N m.+1 (value m.+1 (td m phi) x).
Proof.
move=>hx;rewrite (@current_scalar_product_derivative_values R h2 n m U hU gamma phi x hx).
apply:(le_trans (real_seminorm_triangle (@current_form_comass_real_norm R h2 n m.+1).1 _ _)).
apply:lerD.
- exact:current_one_form_comass_wedge_bound.
- exact:current_zero_form_comass_wedge_bound.
Qed.
End CurrentScalarProductNorm.
