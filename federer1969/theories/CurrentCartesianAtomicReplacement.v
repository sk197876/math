(** Federer (1969), 4.1.23, p. 380:
    replacing the transverse positive zero-current
    by its equal-mass atomic approximation
    gives the printed product flat bound
    and preserves the rectangle's exact mass.
    The original Cartesian support index is retained. *)
From mathcomp Require Import all_boot all_order all_algebra
  classical_sets reals constructive_ereal topology.
From Federer Require Import Hom Bilinear RealNormUP NormDifferentialUP InnerNorm
  HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  EuclideanCartesianMap CurrentSpaces SmoothCompactSet CurrentCartesianDomain
  CurrentCartesianProductSealed CurrentCartesianProductBilinear
  CurrentFlatNorm CurrentFlatDualSeminormBasic CurrentFlatCartesianFiniteUpper
  CurrentMassSealed CurrentMassBasic CompactRepresentedCurrentMass NormalCurrentsUP
  CurrentNormalMass CurrentCartesianZeroFactorMass.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section AtomicReplacement.
Variable R : realType.
Hypothesis h2 : (1+1:R)!=0.
Variables m n i : nat.
Variables (A : set (R_n R m)) (B : set (R_n R n)).
Hypothesis hA : forall x, A x -> norm_domain_interior
  (inner_norm (@euclidean_inner_productP R m)) A x.
Hypothesis hB : forall x, B x -> norm_domain_interior
  (inner_norm (@euclidean_inner_productP R n)) B x.
Local Notation hNX := (inner_norm_real_norm (@euclidean_inner_productP R m)).
Local Notation hNY := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation hNZ := (inner_norm_real_norm (@euclidean_inner_productP R (m+n))).
Local Notation AB := (@euclidean_cartesian_set R m n A B).
Local Notation hAB := (@current_cartesian_domain_open R m n A B hA hB).
Variables (KA : smooth_compact_set hNX A) (KB : smooth_compact_set hNY B)
  (KAB : smooth_compact_set hNZ AB).
Hypothesis hKAB : smooth_compact_carrier KAB=
  @euclidean_cartesian_set R m n (smooth_compact_carrier KA) (smooth_compact_carrier KB).
Local Notation CA := (@current_space R h2 m A hA i).
Local Notation CB := (@current_space R h2 n B hB 0%N).
Local Notation P := (@CartesianCurrentProduct.value R h2 m n i 0%N A B hA hB).
Local Notation FB := (@current_flat_norm R h2 n 0%N B hB KB).
Local Notation FAB := (@current_flat_norm R h2 (m+n) (i+0) AB hAB KAB).
Local Notation MC := (@CurrentMass.value R h2 (m+n) (i+0) AB hAB).

(** Source for [current_cartesian_atomic_replacement]:
    F_A(R times S-R times Q)<=N(R)t
    whenever F_B(S-Q)<=t, and
    M(R times Q)=M(R times S)
    whenever M(Q)=M(S), exactly the
    two separate estimates in Federer
    4.1.23, p. 380. Finiteness
    and normality concern the chosen
    rectangle factors, not the original flat input. *)
Theorem current_cartesian_atomic_replacement (T : CA) (S Q : CB)
    (hNormal : @is_normal_current R h2 m A hA i T)
    (hSupport : @current_support R h2 m A hA i T `<=` smooth_compact_carrier KA)
    (normalMass mass t : R) :
  @current_normal_mass R h2 m A hA i T=normalMass%:E ->
  @CurrentMass.value R h2 n 0%N B hB S=mass%:E ->
  @CurrentMass.value R h2 n 0%N B hB Q=mass%:E ->
  (FB (S-Q)<=t%:E)%E ->
  (FAB (P T S-P T Q)<=(normalMass*t)%:E)%E /\ MC (P T Q)=MC (P T S).
Proof.
move=> hN hMassS hMassQ hError.
have hFiniteError : (FB (S-Q)< +oo)%E := le_lt_trans hError (ltry t).
have [b [hb hBValue]] := @current_flat_dual_finite_value R h2 n 0%N B hB KB
  (@current_value R h2 n B hB 0%N (S-Q)) hFiniteError.
have hFlatValue : FB (S-Q)=b%:E := hBValue.
have hBT : b<=t by move: hError; rewrite hFlatValue lee_fin.
have hNonnegative : 0<=normalMass.
  have h := @current_normal_mass_nonnegative R h2 m A hA i T.
  by rewrite hN lee_fin in h.
have hBound := @current_flat_cartesian_finite_upper R h2 m n A B hA hB
  KA KB KAB hKAB i 0%N T (S-Q) normalMass b hN hFlatValue hSupport.
have hLinear := (@current_cartesian_product_bilinear R h2 m n i 0%N A B hA hB).2 T.
rewrite (linB hLinear) in hBound.
have hFiniteMass := @compact_represented_current_finite_mass R h2 m i A hA
  T hNormal.1.1 hNormal.2.
have [a [_ hMassT]] := @current_finite_mass_value R h2 m i A hA T hFiniteMass.
have hMS := @current_cartesian_zero_factor_mass R h2 m n i A B hA hB T S
  a mass hMassT hMassS.
have hMQ := @current_cartesian_zero_factor_mass R h2 m n i A B hA hB T Q
  a mass hMassT hMassQ.
split.
- have hProduct : normalMass*b<=normalMass*t :=
    @ler_wpM2l R normalMass hNonnegative b t hBT.
  have hProductE : ((normalMass*b)%:E<=(normalMass*t)%:E)%E.
    by rewrite lee_fin; exact: hProduct.
  exact: le_trans hBound hProductE.
- exact: eq_trans hMQ (esym hMS).
Qed.
End AtomicReplacement.
