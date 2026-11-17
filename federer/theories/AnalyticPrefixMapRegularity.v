(** Federer (1969), 3.4.8(1), p. 326:
    the original coordinate projection and inclusion are
    analytic. Finite source bases prove boundedness;
    the proved bounded-linear analytic theorem then applies. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import Hom RealNormUP LinearBasis GrassmannAbbreviations FiniteCoordinates
  EuclideanInnerProduct InnerNorm HilbertFormCompactness NormDifferentialUP NormOpenDomainLaws
  NormFiniteLinearBound NormAnalyticUP NormAnalyticLinear.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [analytic_prefix_projection_analytic]: every
    original finite-dimensional linear projection is analytic
    on its whole source, supporting 3.4.8(1), p. 326. *)
Theorem analytic_prefix_projection_analytic (R:realType) (X:lmodType R)
    (NX:X->R) (hNX:is_real_norm NX) n (e:'I_n->X) j (P:Hom X (R_n R j)):
  is_basis e ->
  @norm_analytic R X (R_n R j) NX (inner_norm (@euclidean_inner_productP R j))
    hNX (inner_norm_real_norm (@euclidean_inner_productP R j)) setT P.
Proof.
move=>he.
apply:(@norm_bounded_linear_analytic R X (R_n R j) NX
  (inner_norm (@euclidean_inner_productP R j)) hNX
  (inner_norm_real_norm (@euclidean_inner_productP R j)) setT
  (fun x _=>norm_full_domain_interior NX x) P).
exact:(@norm_finite_linear_bounded R X (R_n R j) NX
  (inner_norm (@euclidean_inner_productP R j)) hNX
  (inner_norm_real_norm (@euclidean_inner_productP R j)) n e he P).
Qed.

(** Source for [analytic_prefix_inclusion_analytic]: every
    auxiliary coordinate inclusion is analytic on its
    whole original coordinate space, supporting
    3.4.8(1),(5), pp. 326, 328. *)
Theorem analytic_prefix_inclusion_analytic (R:realType) (X:lmodType R)
    (NX:X->R) (hNX:is_real_norm NX) j (S:Hom (R_n R j) X):
  @norm_analytic R (R_n R j) X (inner_norm (@euclidean_inner_productP R j)) NX
    (inner_norm_real_norm (@euclidean_inner_productP R j)) hNX setT S.
Proof.
apply:(@norm_bounded_linear_analytic R (R_n R j) X
  (inner_norm (@euclidean_inner_productP R j)) NX
  (inner_norm_real_norm (@euclidean_inner_productP R j)) hNX setT
  (fun z _=>norm_full_domain_interior (inner_norm (@euclidean_inner_productP R j)) z) S).
exact:(@norm_finite_linear_bounded R (R_n R j) X
  (inner_norm (@euclidean_inner_productP R j)) NX
  (inner_norm_real_norm (@euclidean_inner_productP R j)) hNX j
  (@coordinate_basis R j) (@coordinate_basisP R j) S).
Qed.
