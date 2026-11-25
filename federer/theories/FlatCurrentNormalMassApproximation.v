(** Federer (1969), 4.1.23, p. 379: the
    first reduction keeps the original compact index
    while controlling both flat error and mass.
    Finite input mass uses 4.1.17; infinite input
    mass uses the original normal flat closure,
    so no finite-mass premise enters the theorem. *)
From mathcomp Require Import all_boot all_order all_algebra
  classical_sets reals constructive_ereal topology.
From Federer Require Import Hom RealNormUP NormDifferentialUP InnerNorm
  HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  CurrentSpaces CurrentSupportGeometry SmoothCompactSet
  NormalCurrentsUP CurrentMassSealed CurrentMassBasic CurrentMassFiniteAlgebra
  CurrentFiniteMassLinearBound CurrentFlatNorm CurrentFlatMassComparison
  CurrentFlatCompactMonotone FlatCurrentsUP FlatCurrentFinite
  FlatFiniteMassClosure.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section NormalMassApproximation.
Variable R : realType.
Hypothesis h2 : (1+1:R)!=0.
Variables n m : nat.
Local Notation X := (R_n R n).
Local Notation NX := (inner_norm (@euclidean_inner_productP R n)).
Local Notation hNX := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Variable U : set X.
Hypothesis hU : forall x, U x -> norm_domain_interior NX U x.
Local Notation Current := (@current_space R h2 n U hU m).
Local Notation M := (@CurrentMass.value R h2 n m U hU).
Local Notation support := (@current_support R h2 n U hU m).

(** Source for [flat_current_normal_flat_mass_approximation]:
    the first reduction in Federer 4.1.23,
    p. 379, on the original U.
    The normal approximant stays in K, its
    error is measured in any containing compact C,
    and its mass is at most M(T)+delta,
    also when the original M(T) is infinite. *)
Theorem flat_current_normal_flat_mass_approximation
    (K C : smooth_compact_set hNX U) (T : Current) (delta : R) :
  smooth_compact_carrier K `<=` smooth_compact_carrier C ->
  @is_flat_current_supported_in R h2 n m U hU K T -> 0<delta ->
  exists Q : Current,
    @normal_currents_supported_in R h2 n U hU m K Q /\
    (@current_flat_norm R h2 n m U hU C (T-Q)%R<delta%:E)%E /\
    (M Q<=M T+delta%:E)%E.
Proof.
move=> hKC hFlat hDelta.
case: (ltP (M T) (+oo%E))=> hFinite.
- have [Q [hQ hError]] := @flat_finite_mass_normal_approximation
    R h2 n m U hU K T hFlat hFinite delta hDelta.
  have hSupportT := @flat_current_supported_support R h2 n m U hU K T hFlat.
  have hDifference : support (T-Q)%R `<=` smooth_compact_carrier K.
    have h := @current_support_linear_subset R h2 n m U hU K
      (-1) Q T hQ.2 hSupportT.
    by rewrite scaleN1r addrC in h.
  have hFirst := @current_flat_norm_le_mass R h2 n m U hU K (T-Q)%R hDifference.
  have hMonotone := @current_flat_compact_monotone R h2 n m U hU K C hKC (T-Q)%R.
  have hFlatError := le_lt_trans (le_trans hMonotone hFirst) hError.
  have [a [hA hMassValue]] := @current_finite_mass_value R h2 n m U hU T hFinite.
  have hMassUpper : (M T<=a%:E)%E by rewrite hMassValue.
  have hUpper := @current_finite_mass_linear_bound R h2 n m U hU
    (-1) (T-Q)%R T delta a (ltW hError) hMassUpper.
  have hIdentity : (-1)*:(T-Q)+T=Q by rewrite scaleN1r opprB subrK.
  rewrite hIdentity normrN normr1 mul1r in hUpper.
  exists Q; split; first exact: hQ.
  split; first exact: hFlatError.
  by rewrite hMassValue -EFinD addrC.
- have [Q [hQ hError]] := @hFlat delta hDelta.
  have hMonotone := @current_flat_compact_monotone R h2 n m U hU K C hKC (T-Q)%R.
  have hInfinity : M T=+oo%E by apply/eqP; rewrite eq_le hFinite leey.
  exists Q; split; first exact: hQ.
  split; first exact: le_lt_trans hMonotone hError.
  by rewrite hInfinity addye // leey.
Qed.
End NormalMassApproximation.
