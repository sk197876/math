(** Federer (1969), 3.1.13, p. 225:
    the zeroth-order term in the Leibniz
    formula is scalar multiplication by sigma(x).
    This is the degree-zero convention of
    1.10.1–1.10.2, pp. 44–45. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import Hom BoundedHom ScalarCoefficients Bilinear RealNormUP
  SymmetricForms SymmetricFormZero SymmetricFormSum SymmetricFormProduct SymmetricFormUnit
  ContinuousMultilinearUP ContinuousMultilinearZero NormHigherDifferentialUP NormHigherSymmetricFormUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [scalar_symmetric_coefficient_product]:
    the degree-zero factor c acts on
    scalar-valued symmetric forms by ordinary
    scalar multiplication, used in Federer
    3.1.13, p. 225. *)
Lemma scalar_symmetric_coefficient_product (K : fieldType) (X : lmodType K)
    (c : K) (H : S_star X K^o) :
  symmetric_forms_product (ScalarCoefficients.scalar_bilinear K)
    (sform_include (zero_sform X (c : K^o))) H=c*:(H : Hom_finite _ _).
Proof.
have he : symmetric_coefficient_form X (c : K^o)=c*:symmetric_coefficient_form X (1 : K^o).
  rewrite -linearZ; congr (symmetric_coefficient_form X _); exact: (esym (mulr1 c)).
change (symmetric_forms_product (ScalarCoefficients.scalar_bilinear K)
  (symmetric_coefficient_form X (c : K^o)) H=c*:(H : Hom_finite _ _)).
rewrite he (bilZl (symmetric_forms_product_bilinear _ (ScalarCoefficients.scalar_bilinear K))).
congr (c*:_).
exact: (symmetric_forms_unit_left (ScalarCoefficients.scalar_bilinear K) (@mul1r K) H).
Qed.

(** Source for [norm_zeroth_differential_form_value]:
    the zeroth differential is the function's
    value, so its symmetric form is
    the corresponding constant zero-form, Federer
    3.1.11, pp. 218–220,
    applied in 3.1.13, p. 225. *)
Lemma norm_zeroth_differential_form_value (R : realType)
    (X Y : lmodType R) (NX : X->R)
    (Z : nat->lmodType R)
    (ev : forall i, {ffun 'I_i->X}->Hom (Z i) Y)
    (ZN : forall i, Z i->R)
    (A : X->Prop) (f : X->Y) a (phi : S_m X Y 0%N) :
  is_norm_higher_differential_form NX ev ZN A f 0%N a phi ->
  phi=zero_sform X (f a).
Proof.
move=>[z [[ha hz] he]].
apply: sform_ext=>t; rewrite (tuple0 t) zero_sformE.
have hh := he [ffun i : 'I_0=>(0:X)].
have ht : [tuple [ffun i : 'I_0=>(0:X)] j | j<0]=[tuple].
  exact: tuple0.
by rewrite ht hz in hh.
Qed.
