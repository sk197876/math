(** Federer (1969), 3.4.11, p. 338:
    the independent leading-term laws imply the actual
    homogeneous polynomial, its continuity, dilation equation
    and zero value at the origin. These are
    proved properties, rather than fields of the specification. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import Hom RealNormUP NormClassOneUP AnalyticGermUP AnalyticGermRingLaws
  AnalyticInitialPolynomialUP AnalyticInitialTaylorRemainder HomogeneousPolynomialFunctions
  NormPolynomialCoefficientBall AnalyticGermValueSealed AnalyticInitialPolynomialGermUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [analytic_initial_polynomial_laws]: the
    actual leading Taylor polynomial in 3.4.11,
    p. 338, is continuous, homogeneous of the
    exact positive degree and zero at the origin. *)
Theorem analytic_initial_polynomial_laws (R:realType) (X:lmodType R)
    (NX:X->R) (hNX:is_real_norm NX)
    (alpha:analytic_germ_space hNX (0:X)) k (P:X->R):
  is_initial_analytic_germ_polynomial alpha k P ->
  @is_homogeneous_polynomial R X R^o k P /\
  norm_class_zero NX (fun t:R^o=>`|t|) (fun _=>True) P /\
  (forall (t:R) v,P (t*:v)=t^+k*P v) /\P 0=0.
Proof.
move=>hInitial.
have [f hF]:=@analytic_germ_has_representative R X NX hNX 0 alpha.
have [hPolynomial [hContinuous [hScale _]]]:=
  @analytic_initial_taylor_remainder R X NX hNX alpha k P f hInitial hF.
split;first exact:hPolynomial.
split;first exact:hContinuous.
split;first exact:hScale.
exact:(@positive_homogeneous_polynomial_zero R X R^o k P hInitial.1 hPolynomial).
Qed.

(** Source for [analytic_initial_polynomial_germ_zero_value]:
    every original initial polynomial germ has zero
    centre value, supporting properness of its generated
    ideal in 3.4.11, p. 338. *)
Lemma analytic_initial_polynomial_germ_zero_value (R:realType) (X:lmodType R)
    (NX:X->R) (hNX:is_real_norm NX)
    (alpha beta:analytic_germ_space hNX (0:X)):
  is_initial_polynomial_germ alpha beta ->
  @AnalyticGermValue.map R X NX hNX 0 beta=0.
Proof.
move=>[k [P [f [hInitial [hValues <-]]]]].
rewrite (@AnalyticGermValue.laws R X NX hNX 0 f) hValues.
exact:(analytic_initial_polynomial_laws hInitial).2.2.2.
Qed.
