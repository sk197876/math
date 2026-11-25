(** Federer (1969), 3.4.5, p. 321: actual
    coordinate monomials in the cubic-cone polynomial argument.
    Their polynomial representations are the original symmetric
    forms of 1.10.4, pp. 45–47. *)
From mathcomp Require Import all_boot all_order all_algebra boolp reals.
From Federer Require Import Hom GrassmannAbbreviations PolynomialFunctions PolynomialLinearComposition
  ScalarPowerAnalytic EuclideanScalarCoordinateMaps.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [euclidean_coordinate_power_polynomial]:
    every original coordinate power is a polynomial,
    supporting the cubic coefficients in 3.4.5, p. 321.
    Degree zero and every finite coordinate are retained. *)
Lemma euclidean_coordinate_power_polynomial (R:realType) n (i:'I_n) q:
  @is_polynomial_function R (R_n R n) R^o (fun v=>(v i)^+q).
Proof.
have [P hP]:=@scalar_power_polynomial_exists R q.
have hPolynomial:=elimT (asboolP _) (polynomial_function_proof P).
have [F hF]:=@polynomial_linear_precompose R (R_n R n) R^o R^o
  (hom_as_linear (euclidean_scalar_coordinate_map i)) P hPolynomial.
exists F=>v;rewrite -hF hom_as_linearE hP.
reflexivity.
Qed.

(** Source for [euclidean_coordinate_polynomial]: the
    original coordinate itself is polynomial, supporting
    finite monic division in 3.4.5, p. 321. *)
Lemma euclidean_coordinate_polynomial (R:realType) n (i:'I_n):
  @is_polynomial_function R (R_n R n) R^o (fun v=>v i).
Proof.
have [F hF]:=@euclidean_coordinate_power_polynomial R n i 1%N.
exists F=>v;by rewrite -hF expr1.
Qed.
