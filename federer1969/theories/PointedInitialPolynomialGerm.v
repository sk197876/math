(** Federer (1969), 3.4.11, p. 338:
    onto linear substitutions carry actual leading polynomial
    germs to the leading polynomial germs of the
    substituted original germs. The existing representative
    pullback and full derivative laws prove the statement. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import Hom RealNormUP AnalyticGermUP AnalyticGermRepresentatives
  PointedAnalyticPullbackUP AnalyticInitialPolynomialUP AnalyticInitialPolynomialGermUP
  PointedLinearInitialPolynomial.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [pointed_initial_polynomial_germ]: the
    original leading polynomial commutes with onto linear
    coordinate substitutions in 3.4.11, p. 338.
    The actual representative equation and the actual
    least nonzero derivative order are conclusions. *)
Theorem pointed_initial_polynomial_germ (R:realType) (X Y:lmodType R)
    (NX:X->R) (NY:Y->R) (hNX:is_real_norm NX) (hNY:is_real_norm NY)
    (L:Hom X Y)
    (F:analytic_germ_space hNY (0:Y)->analytic_germ_space hNX (0:X)):
  is_pointed_analytic_germ_pullback L F ->(forall y,exists x,L x=y) ->
  forall alpha beta,is_initial_polynomial_germ alpha beta ->
    is_initial_polynomial_germ (F alpha) (F beta).
Proof.
move=>hF hOnto alpha beta [k [P [f [hInitial [hValues hGerm]]]]].
have [g [hPull hComposition]]:=hF f.
exists k,(fun x=>P (L x)),g;split.
- exact:(@pointed_linear_initial_polynomial R X Y NX NY hNX hNY L F hF k alpha P hOnto hInitial).
- split;first by move=>x;rewrite hComposition hValues.
  by rewrite -hPull hGerm.
Qed.
