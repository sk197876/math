(** Federer (1969), 3.4.7, p. 325: the
    actual analytic germ ring on R^n is Noetherian
    at every original centre. This is the original
    Euclidean specialization of the proved finite-source induction. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct
  InnerNorm HilbertFormCompactness RealNormUP AnalyticGermRing CommutativeIdealUP AnalyticGermNoetherian.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [euclidean_analytic_germ_ring_noetherian]:
    the full original Noetherian assertion for O_a(R^n)
    in 3.4.7, p. 325. Every natural source
    dimension and every original centre remain; the
    original coordinate basis supplies finite dimension. *)
Theorem euclidean_analytic_germ_ring_noetherian (R:realType) n (a:R_n R n):
  is_noetherian_commutative_ring [the comNzRingType of
    (@analytic_germ_ring R (R_n R n) (inner_norm (@euclidean_inner_productP R n))
      (inner_norm_real_norm (@euclidean_inner_productP R n)) a)].
Proof.
exact:(@finite_analytic_germ_ring_noetherian R (R_n R n)
  (inner_norm (@euclidean_inner_productP R n))
  (inner_norm_real_norm (@euclidean_inner_productP R n)) n (@coordinate_basis R n) a
  (@coordinate_basisP R n)).
Qed.
