(** Federer (1969), 3.4.5, p. 321: an actual
    polynomial vanishing along a positive half-ray vanishes
    at its endpoint. This internal coefficient argument
    supports the cited analytic counterexample. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import TensorUP Hom PolynomialFunctions PolynomialSliceCoefficients PolynomialCoefficientUniqueness
  PositivePolynomialCoefficientUniqueness PolynomialSliceNullCoefficients.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [polynomial_positive_half_ray_endpoint]:
    positive scalar restriction supplies enough actual roots
    for finite coefficient uniqueness, supporting the cubic-cone
    argument of 3.4.5, p. 321. *)
Lemma polynomial_positive_half_ray_endpoint (R:realType) (X Y:lmodType R)
    (P:PolynomialFunction X Y) (a v:X):
  (forall t:R,0<t ->P (a+t*:v)=0) ->P a=0.
Proof.
move=>hZero.
pose g:=@linear_id R X.
pose s:=polynomial_slice_list P g v a.
have hValue t:coefficient_polynomial_value s t = P (a+t*:v).
  exact:(@polynomial_slice_horner R (@Num.Theory.pchar_num R) X X Y P g v a t).
have hCoefficients:all (pred1 0) s.
  apply:positive_coefficient_polynomial_zero=>t ht.
  by rewrite hValue hZero.
have hAtZero:=@coefficient_polynomial_all_zero R Y s 0 hCoefficients.
by rewrite hValue scale0r addr0 in hAtZero.
Qed.
