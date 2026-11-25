(** Federer (1969), 4.1.23, p. 379: reduce
    the original theorem to normal inputs without
    discarding its mass estimate or infinite-mass case.
    The normal-input assertion is an explicit premise
    of this supporting reduction, not a new axiom
    or a hypothesis of the final theorem. *)
From mathcomp Require Import all_boot all_order all_algebra
  classical_sets reals constructive_ereal topology lra.
From Federer Require Import Hom RealNormUP NormDifferentialUP InnerNorm
  HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  CurrentSpaces SmoothCompactSet NormalCurrentsUP CurrentMassSealed
  CurrentFlatNorm CurrentFlatFiniteArithmetic FlatCurrentsUP
  FlatCurrentNormalMassApproximation PolyhedralApproximationUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section NormalReduction.
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
Variables K C : smooth_compact_set hNX U.
Hypothesis hKC : smooth_compact_carrier K `<=` smooth_compact_carrier C.
Local Notation F := (@current_flat_norm R h2 n m U hU C).
Local Notation spec := (@is_polyhedral_flat_mass_approximation R h2 n m U hU C).

(** Source for [flat_current_polyhedral_normal_reduction]:
    the first proof reduction of Federer
    4.1.23, p. 379, with both
    printed conclusions retained. The same original
    K and C are used throughout, and
    no finite M(T) premise is added. *)
Theorem flat_current_polyhedral_normal_reduction :
  (forall Q : Current,
    @normal_currents_supported_in R h2 n U hU m K Q ->
    forall delta : R, 0<delta -> exists P : Current, spec Q delta P) ->
  forall T : Current,
    @is_flat_current_supported_in R h2 n m U hU K T ->
    forall epsilon : R, 0<epsilon -> exists P : Current, spec T epsilon P.
Proof.
move=> hNormalApprox T hFlat epsilon hEpsilon.
pose delta := epsilon/3.
have hThree : 0<(3:R) by rewrite ltr0n.
have hDelta : 0<delta := divr_gt0 hEpsilon hThree.
have hBudget : delta+delta<=epsilon by rewrite /delta; lra.
have [Q [hQ [hError hMass]]]:=@flat_current_normal_flat_mass_approximation
  R h2 n m U hU K C T delta hKC hFlat hDelta.
have [P [hPoly [hFlatError hPolyMass]]] := @hNormalApprox Q hQ delta hDelta.
have hFirstFinite : (F (T-Q)%R< +oo)%E := lt_trans hError (ltry delta).
have hSecondFinite : (F (Q-P)%R< +oo)%E := le_lt_trans hFlatError (ltry delta).
have hTriangle := @current_flat_finite_triangle R h2 n m U hU C
  (T-Q)%R (Q-P)%R hFirstFinite hSecondFinite.
have hIdentity : (T-Q)+(Q-P)=T-P by rewrite addrA subrK.
rewrite hIdentity in hTriangle.
have hSum := leeD (ltW hError) hFlatError.
rewrite -EFinD in hSum.
have hFlatResult : (F (T-P)%R<=epsilon%:E)%E.
  apply: (le_trans (le_trans hTriangle hSum)).
  by rewrite lee_fin.
have hMassStep := leeD hMass (lexx delta%:E).
have hFinalMass : (M P<=M T+epsilon%:E)%E.
  apply: (le_trans (le_trans hPolyMass hMassStep)).
  rewrite -addeA -EFinD.
  apply: leeD; first exact: lexx.
  by rewrite lee_fin.
exists P; split; first exact: hPoly.
by split.
Qed.
End NormalReduction.
