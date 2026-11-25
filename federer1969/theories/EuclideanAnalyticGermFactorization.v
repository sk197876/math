(** Federer (1969), 3.4.7, p. 325: the
    actual analytic germ ring on R^n is a unique-factorization domain
    at every original centre. This is the original
    Euclidean specialization of the proved finite-source induction. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct
  InnerNorm HilbertFormCompactness RealNormUP AnalyticGermRing CommutativeFactorizationUP AnalyticGermFactorization.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [euclidean_analytic_germ_ring_factorization]:
    the full original unique-factorization assertion for O_a(R^n)
    in 3.4.7, p. 325. Every natural source
    dimension and every original centre remain; the
    original coordinate basis supplies finite dimension. *)
Theorem euclidean_analytic_germ_ring_factorization (R:realType) n (a:R_n R n):
  is_unique_factorization_commutative_domain [the comNzRingType of
    (@analytic_germ_ring R (R_n R n) (inner_norm (@euclidean_inner_productP R n))
      (inner_norm_real_norm (@euclidean_inner_productP R n)) a)].
Proof.
exact:(@finite_analytic_germ_ring_factorization R (R_n R n)
  (inner_norm (@euclidean_inner_productP R n))
  (inner_norm_real_norm (@euclidean_inner_productP R n)) n (@coordinate_basis R n) a
  (@coordinate_basisP R n)).
Qed.
