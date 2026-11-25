(** Federer (1969), 3.4.5, p. 321: internal
    finite coordinate expansions used in the cubic-cone
    argument for the cited analytic counterexample. All
    coefficients come from the original polynomials of 1.10.4. *)
From mathcomp Require Import all_boot all_order all_algebra boolp reals.
From Federer Require Import Hom FiniteCoordinates GrassmannAbbreviations EuclideanInnerProduct EuclideanCoordinateTopology HilbertFormCompactness
  HomogeneousPolynomialFunctions PolynomialFunctions PolynomialRepresentations PolynomialTaylor
  PolynomialSliceCoefficients EuclideanPolynomialSlices EuclideanCoordinateSplit.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [euclidean_polynomial_slice_sum]: the
    actual first-coordinate power expansion from 1.10.4,
    p. 46, supporting the example cited in 3.4.5, p. 321. *)
Lemma euclidean_polynomial_slice_sum (R:realType) n
    (P:PolynomialFunction (R_n R n.+1) R^o) (v:R_n R n.+1):
  P v=\sum_(i<(polynomial_degree P).+1)
    (v ord0)^+i*euclidean_polynomial_coefficient P i (coordinate_tail v).
Proof.
rewrite -[in LHS](euclidean_splitK v) euclidean_join_as_line.
exact:(@polynomial_slice_expansion R (@pchar_num R) (R_n R n) (R_n R n.+1) R^o P
  (GRing.Linear.clone R (R_n R n) (R_n R n.+1) *:%R (@coordinate_tail_inclusion R n) _)
  (@coordinate_head_inclusion R n 1) (coordinate_tail v) (coordinate_head v)).
Qed.

(** Source for [univariate_euclidean_polynomial_power_expansion]:
    every actual line polynomial has finite scalar power
    coefficients, supporting the cubic-cone example cited in
    3.4.5, p. 321. Its constant coefficient is retained. *)
Theorem univariate_euclidean_polynomial_power_expansion (R:realType)
    (P:PolynomialFunction (R_n R 1) R^o):
  exists N (a:nat->R),(0<N)%N /\forall v:R_n R 1,
    P v=\sum_(i<N) a i*(v ord0)^+i.
Proof.
pose a i:=sform_polynomial_value (polynomial_taylor_coefficient P i 0)
  (@coordinate_basis R 1 ord0).
exists (polynomial_degree P).+1,a;split;first exact:ltn0Sn.
move=>v.
have hCoordinates:v=0+(v ord0)*:(@coordinate_basis R 1 ord0).
  rewrite add0r;have h:=@euclidean_coordinate_expansion R 1 v.
  by rewrite big_ord1 in h.
rewrite {1}hCoordinates (polynomial_taylor_formula (@pchar_num R)).
apply:eq_bigr=>i _;rewrite sform_polynomial_scale_argument.
change ((v ord0)^+i*a i=a i*(v ord0)^+i).
exact:mulrC.
Qed.
