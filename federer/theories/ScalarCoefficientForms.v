(** Federer (1969), 3.1.24, pp. 239–240: scalar
    derivative forms are the product form times their scalar
    derivative coefficient. This supplies the common interface
    for the scalar composition and inverse calculations. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import TensorUP Hom SymmetricForms SymmetricFunctionalProduct HomogeneousPolynomialFunctions
  PolynomialDiagonalNorm NormHigherDifferentialUP NormHigherSymmetricFormUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [scalar_coefficient_form]: supporting the
    scalar specializations in Federer 3.1.24, pp. 239–240.
    The degree-m form with coefficient c sends its arguments
    to c times their product, including the empty product. *)
Definition scalar_coefficient_form (K:fieldType) m (c:K):S_m K^o K^o m :=
  c*:symmetric_functional_product_form (linear_id K^o) m.

(** Source for [scalar_coefficient_form_unit]: the coefficient
    is precisely the form's value on unit arguments, supporting
    the scalar inverse calculation in Federer 3.1.24, p. 240. *)
Lemma scalar_coefficient_form_unit (K:fieldType) m (c:K) :
  scalar_coefficient_form m c [tuple (1:K^o) | i<m]= c.
Proof.
rewrite /scalar_coefficient_form sform_scaleE symmetric_functional_product_formE.
have hp:(\prod_(i<m) (linear_id K^o) (tnth [tuple (1:K^o) | j<m] i))= 1.
  apply:big1=>i _; by rewrite tnth_mktuple.
change (c*(\prod_(i<m) (linear_id K^o) (tnth [tuple (1:K^o) | j<m] i))= c).
by rewrite hp mulr1.
Qed.

(** Source for [scalar_coefficient_form_polynomial_unit]: the
    normalized scalar coefficient is c/m!, supporting the
    recurrence computation in Federer 3.1.24, pp. 239–240.
    Characteristic-zero applications guarantee nonzero factorials. *)
Lemma scalar_coefficient_form_polynomial_unit (K:fieldType) m (c:K) :
  sform_polynomial_value (scalar_coefficient_form m c) 1= c/(m`!)%:R.
Proof.
rewrite sform_polynomial_diagonal_value scalar_coefficient_form_unit.
change ((m`!)%:R^-1*c=c*(m`!)%:R^-1); exact:mulrC.
Qed.

(** Source for [scalar_coefficient_form_actual]: supporting
    the actual scalar derivative forms used in Federer
    3.1.24, pp. 239–240. An actual higher differential
    whose evaluation is the product of its scalar arguments
    times c is represented by the stated product form. *)
Lemma scalar_coefficient_form_actual (R:realType)
    (Z:nat->lmodType R) (ev:forall i,{ffun 'I_i->R^o}->Hom (Z i) R^o)
    (ZN:forall i,Z i->R) (A:R^o->Prop) (f:R^o->R^o) m a (z:Z m) c :
  has_norm_higher_differential (fun t:R^o=>`|t|) ev ZN A f m a z ->
  (forall u,@ev m u z=(\prod_(i<m) u i)*c) ->
  is_norm_higher_differential_form (fun t:R^o=>`|t|) ev ZN A f m a (scalar_coefficient_form m c).
Proof.
move=>hz he; exists z; split; first exact hz.
move=>u; rewrite he /scalar_coefficient_form sform_scaleE symmetric_functional_product_formE.
change ((\prod_(i<m) u i)*c=c*\prod_(i<m) tnth [tuple u j | j<m] i).
have hp:(\prod_(i<m) tnth [tuple u j | j<m] i)=\prod_(i<m) u i.
  by apply:eq_bigr=>i _; rewrite tnth_mktuple.
by rewrite hp mulrC.
Qed.
