(** Federer (1969), 2.6.5, p. 120, final induction on Euclidean dimension.
    The scalar variable is the first coordinate and the remaining
    coordinates form the smaller Euclidean space. Coefficients come from the
    Taylor theorem of 1.10.4, p. 46, not an alternate polynomial definition. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import Bilinear FiniteCoordinates GrassmannAbbreviations EuclideanInnerProduct InnerMetric
  EuclideanCoordinateSplit PolynomialFunctions PolynomialRepresentations PolynomialCoefficientUniqueness
  PolynomialSliceCoefficients.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Section Slices.
Variable R : realType.
Variable n : nat.
Local Notation V := (R_n R n.+1).
Local Notation U := (R_n R n).
Local Notation g := (GRing.Linear.clone R U V *:%R (@coordinate_tail_inclusion R n) _).
Local Notation e := (@coordinate_head_inclusion R n 1).

(** Source for [euclidean_join_as_line]: supporting
    coordinate form g(u)+t e of the splitting used in
    Federer 2.6.5, p. 120, for Taylor's formula. *)
Lemma euclidean_join_as_line (u : U) (t : R) : euclidean_join (u,t) = g u + t *: e.
Proof.
rewrite /euclidean_join /=; congr (_ + _).
have h := linZ (@coordinate_head_inclusion_linear R n) t (1 : R^o).
change (@coordinate_head_inclusion R n (t*1) = t *: e) in h.
by rewrite mulr1 in h.
Qed.

Variable P : PolynomialFunction V R^o.

(** Source for [euclidean_polynomial_coefficient]: scalar
    coefficient polynomial in the remaining n coordinates,
    supporting Federer 2.6.5, p. 120, via 1.10.4,
    p. 46. *)
Definition euclidean_polynomial_coefficient := @polynomial_slice_coefficient R U V R^o P g e.

(** Source for [euclidean_polynomial_coefficient_polynomial]:
    the coefficient functions to which the smaller-dimensional
    induction applies in Federer 2.6.5, p. 120,
    are polynomials in the existing Chapter 1 sense. *)
Lemma euclidean_polynomial_coefficient_polynomial i :
  is_polynomial_function (euclidean_polynomial_coefficient i).
Proof. exact (@polynomial_slice_coefficient_polynomial R (@pchar_num R) U V R^o P g e i). Qed.

(** Source for [euclidean_polynomial_coefficients]: finite
    coefficient list of the scalar slice in Federer
    2.6.5, p. 120, retaining the constant term. *)
Definition euclidean_polynomial_coefficients (u : U) :=
  [seq euclidean_polynomial_coefficient i u | i <- iota 0 (polynomial_degree P).+1].

(** Source for [euclidean_polynomial_slice_value]: the
    scalar polynomial evaluated on an actual Cartesian slice,
    supporting the Fubini induction in Federer 2.6.5,
    p. 120. *)
Lemma euclidean_polynomial_slice_value u t :
  coefficient_polynomial_value (euclidean_polynomial_coefficients u) t = P (euclidean_join (u,t)).
Proof.
rewrite euclidean_join_as_line.
exact (@polynomial_slice_horner R (@pchar_num R) U V R^o P g e u t).
Qed.

(** Source for [euclidean_polynomial_nonzero_coefficient]:
    the nonzero coefficient polynomial needed in the
    dimension induction of Federer 2.6.5, p. 120.
    Nonzero is expressed by an actual nonzero value. *)
Lemma euclidean_polynomial_nonzero_coefficient :
  (exists x, P x <> 0) -> exists i, (i < (polynomial_degree P).+1)%N /\
    exists u, euclidean_polynomial_coefficient i u <> 0.
Proof.
move=> [x hx].
apply: (@polynomial_slice_nonzero_coefficient R (@pchar_num R) U V R^o P g e).
exists (coordinate_tail x), (coordinate_head x).
by rewrite -euclidean_join_as_line -/(euclidean_split x) euclidean_splitK.
Qed.
End Slices.
