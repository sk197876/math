(** Federer (1969), 4.1.23, pp. 379–380: keep
    the empty-support and above-dimensional cases before
    selecting any box, point or transverse tag.
    The zero current is an original polyhedral
    chain in every compact index, even empty C. *)
From mathcomp Require Import all_boot all_order all_algebra
  classical_sets reals constructive_ereal topology.
From Federer Require Import Hom RealNormUP NormDifferentialUP InnerNorm
  HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  CurrentSpaces CurrentSupportExtensionality CurrentAboveDimension SmoothCompactSet
  FlatCurrentsUP FlatCurrentFinite CurrentFlatNorm CurrentMassSealed
  CurrentMassFiniteAlgebra PolyhedralCurrentAlgebra PolyhedralApproximationUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section PolyhedralEndpoints.
Variable R : realType.
Hypothesis h2 : (1+1:R)!=0.
Variables n m : nat.
Local Notation X := (R_n R n).
Local Notation NX := (inner_norm (@euclidean_inner_productP R n)).
Local Notation hNX := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Variable U : set X.
Hypothesis hU : forall x, U x -> norm_domain_interior NX U x.
Local Notation C := (@current_space R h2 n U hU m).
Local Notation spec := (@is_polyhedral_flat_mass_approximation R h2 n m U hU).

(** Source for [polyhedral_zero_flat_mass_approximation]: the
    zero input already has the exact zero
    polyhedral approximant in every original compact C,
    supporting all endpoints of 4.1.23, p. 379. *)
Theorem polyhedral_zero_flat_mass_approximation
    (K : smooth_compact_set hNX U) (epsilon : R) :
  0<=epsilon -> spec K (0:C) epsilon (0:C).
Proof.
move=> hEpsilon; split.
- apply: (@integral_polyhedral_current_is_polyhedral R h2 n m U hU K).
  exact: integral_polyhedral_current_zero.
split.
- by rewrite subrr current_flat_norm_zero lee_fin.
- by rewrite !current_mass_zero add0e lee_fin.
Qed.

(** Source for [polyhedral_empty_support_approximation]: an
    original flat current with empty compact support
    is zero, so 4.1.23, p. 379,
    needs no point in K, C or U. *)
Theorem polyhedral_empty_support_approximation
    (K L : smooth_compact_set hNX U) (T : C) (epsilon : R) :
  @is_flat_current_supported_in R h2 n m U hU K T ->
  (forall x, ~smooth_compact_carrier K x) ->
  0<=epsilon -> spec L T epsilon (0:C).
Proof.
move=> hFlat hEmpty hEpsilon.
have hSupport := @flat_current_supported_support R h2 n m U hU K T hFlat.
have hZero : T=0.
  apply: (@current_empty_support_iff_zero R h2 n m U hU T).1=> x hx.
  exact: (@hEmpty x (@hSupport x hx)).
rewrite hZero; exact: polyhedral_zero_flat_mass_approximation hEpsilon.
Qed.

(** Source for [polyhedral_above_dimension_approximation]: the
    original above-dimensional current space is zero,
    retaining every natural degree in 4.1.23,
    p. 379 without an extra nonzero-space premise. *)
Theorem polyhedral_above_dimension_approximation
    (K : smooth_compact_set hNX U) (T : C) (epsilon : R) :
  (n<m)%N -> 0<=epsilon -> spec K T epsilon (0:C).
Proof.
move=> hDegree hEpsilon.
rewrite (@current_above_dimension R h2 n m hDegree U hU T).
exact: polyhedral_zero_flat_mass_approximation hEpsilon.
Qed.
End PolyhedralEndpoints.
