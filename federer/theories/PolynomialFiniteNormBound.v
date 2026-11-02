(** Federer (1969), 1.10.5, p. 48: supporting finite evaluation bound for a
    homogeneous polynomial. Source context: PolynomialNormUP.v. No
    finite-dimensional hypothesis is used; the explicit finite bound on the
    supremum is the only boundedness assumption in this lemma. *)
From mathcomp Require Import all_boot all_order all_algebra reals constructive_ereal.
From Federer Require Import RealNormUP RealNormNormalization HomogeneousPolynomialFunctions
  PolynomialNorm PolynomialNormHomogeneity.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [homogeneous_polynomial_finite_norm_bound]: Federer
    1.10.5, p. 48, the homogeneous estimate with a finite
    upper bound L: |P(x)| <= |x|^m L. *)
Lemma homogeneous_polynomial_finite_norm_bound (R : realType) (V W : lmodType R)
    (NV : V -> R) (NW : W -> R) (hV : is_real_norm NV) (hW : is_real_seminorm NW)
    m (P : V -> W) (hP : is_homogeneous_polynomial m P) L :
  (polynomial_norm (proj1 hV) NW P<=L%:E)%E -> forall x,
    NW (P x) <= (NV x)^+m * L.
Proof.
move=> hL x.
rewrite (@homogeneous_polynomial_normalized_norm R V W NV NW hV hW m P hP x).
apply: ler_wpM2l; first exact: exprn_ge0 (real_seminorm_nonnegative (proj1 hV) x).
apply: (proj1 (polynomial_norm_bound (proj1 hV) NW P L) hL).
exact (@real_norm_normalize_unit R V NV (proj1 hV) x).
Qed.
