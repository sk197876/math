(** Private existence proof for the flat
    exponential in Federer (1969), 3.1.11,
    p. 223. The polynomial recurrence
    remains inside this proof; downstream
    modules use only FlatExponentialSealed. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import ScalarSmoothSequenceUP PolynomialCoefficientUniqueness
  ScalarPolynomialCoefficientCalculus FlatPolynomialExtensionConstruction
  FlatExponentialUP RealExponentialSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [flat_exponential_exists]:
    the function in Federer 3.1.11,
    p. 223, exists, and every
    derivative exists everywhere. Every derivative
    vanishes on the nonpositive half-line.
    The private coefficient recurrence supplies
    the witnesses and all their exact graph laws. *)
Theorem flat_exponential_exists (R : realType) :
  exists f : R->R, is_flat_exponential f /\
    exists F : nat->R->R,
      is_scalar_smooth_derivative_sequence f F /\
      forall k x, x<= 0 -> F k x= 0.
Proof.
pose P k := iter k (@flat_exponential_polynomial_step R) [::1].
pose F k := flat_polynomial_extension (P k).
exists (F 0%N); split.
- constructor.
  + move=> x hx; rewrite /F /P /= /flat_polynomial_extension hx.
    change ((1+x^-1*0)*RealExponential.exponential (-((x^-1)^+2))=
      RealExponential.exponential (-((x^-1)^+2))).
    by rewrite mulr0 addr0 mul1r.
  + move=> x hx; exact: flat_polynomial_extension_nonpositive hx.
- exists F; split.
  + split; first by move=>x.
    move=>k a; have he : P k.+1=flat_exponential_polynomial_step (P k).
      by rewrite /P iterS.
    rewrite /F he; exact: flat_polynomial_extension_differential.
  + move=>k x hx; exact: flat_polynomial_extension_nonpositive hx.
Qed.
