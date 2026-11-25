(** Federer (1969), 1.7.7, p. 34, second displayed formula: the norm of a
    simple m-covector in R^n is the supremum of pullback norms over O(n,m).
    The real supremum convention covers the empty set when m>n. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct
  FiniteCoordinates CoordinateProjection OrthogonalEuclidean InnerNorm
  ExteriorCovectorInner SimpleCovectors AlternatingCoordinates AlternatingDual
  CovectorProjectionNorm NonnegativeSupremum.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Section Supremum.
Variable R : realType.
Hypothesis h2 : (1+1 : R) != 0.
Variables n m : nat.

(** Source for [simple_covector_projection_values]: Federer 1.7.7,
    p. 34, the set in the second displayed supremum formula. *)
Definition simple_covector_projection_values (phi : A_m (R_n R n) R^o m) : set R :=
  [set r | exists f : {linear R_n R m -> R_n R n}, @FedererOrthogonal.O R n m f /\
    r = exterior_covector_norm h2 (@euclidean_inner_productP R m) (@coordinate_basisP R m)
      (A_m_dual f phi)].

(** Source for [simple_covector_projection_supremum]: Federer
    1.7.7, p. 34, second displayed equality. No positive-degree
    or positive-dimension hypothesis is needed. *)
Theorem simple_covector_projection_supremum (phi : A_m (R_n R n) R^o m)
    (sp : simple_covector h2 phi) :
  exterior_covector_norm h2 (@euclidean_inner_productP R n) (@coordinate_basisP R n) phi =
    sup (simple_covector_projection_values phi).
Proof.
apply: nonnegative_supremum_attained_if_nonzero.
- exact: inner_norm_nonnegative.
- move=> r [f [hf ->]]; split; first exact: inner_norm_nonnegative.
  exact: (@orthogonal_covector_pullback_bound R h2 (R_n R m) (R_n R n)
    (@euclidean_inner_product R m) (@euclidean_inner_product R n)
    (@euclidean_inner_productP R m) (@euclidean_inner_productP R n)
    m n (@coordinate_basis R m) (@coordinate_basis R n)
    (@coordinate_basisP R m) (@coordinate_basisP R n) f hf m phi).
- rewrite /exterior_covector_norm inner_norm_eq0 => hp.
  have [f [hf he]] := @simple_covector_pullback_attained R h2 (R_n R n)
    (@euclidean_inner_product R n) (@euclidean_inner_productP R n)
    n (@coordinate_basis R n) (@coordinate_basisP R n) m phi hp sp.
  exists f; split=> //; exact: esym he.
Qed.
End Supremum.
