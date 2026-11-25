(** Federer (1969), 4.1.25, p. 383: construct
    the smooth family in the first proof using 4.1.2,
    p. 347. The original nonnegative normalized kernel
    preserves the Lipschitz bound. Its input differentials
    converge almost everywhere by the preceding directional
    Lebesgue-point argument, without a kernel symmetry premise. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  functions classical_sets reals constructive_ereal topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP
  NormDifferentialLipschitzBound NormRegularity NormClassZeroWhole NormClassOneUP
  GrassmannAbbreviations EuclideanInnerProduct InnerNorm HilbertFormCompactness
  EuclideanHomOperator HomSpaceTopology EuclideanOwnNormCompleteness
  EuclideanLipschitzClassZero LipschitzUP LipschitzBasic
  SmoothingKernelSealed SmoothingDilationSealed SmoothingDilationSmooth
  SmoothingDilationNonzeroRadius SmoothingConvolutionUP ContinuousCompactConvolution
  ContinuousSmoothingSmoothness SmoothingLipschitzBound SmoothingLipschitzError
  CurrentMapDifferential CurrentLipschitzLebesgueActionFamilyUP
  CurrentLipschitzLebesgueActionSmoothingAE
  ReciprocalSequenceLimits ExtendedRealOrderLimit RealErrorOrderLimit
  MeasureAlmostUP MeasureAlmostBasic EuclideanLebesgueDimensions.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section LebesgueActionFamilyExistence.
Variable R : realType.
Variables m n : nat.
Local Notation X := (R_n R m).
Local Notation Y := (R_n R n).
Local Notation NX := (inner_norm (@euclidean_inner_productP R m)).
Local Notation NY := (inner_norm (@euclidean_inner_productP R n)).
Local Notation hNX := (inner_norm_real_norm (@euclidean_inner_productP R m)).
Local Notation hNY := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation phi := (@SmoothingKernel.value R m).
Local Notation hPhi := (@SmoothingKernel.laws R m).
Local Notation family := (@SmoothingDilation.value R m phi).
Local Notation hFamily := (@SmoothingDilation.laws R m phi).
Variable f : X -> Y.
Variable L : R.
Hypothesis hL : 0<=L.
Hypothesis hLip : forall x y, NY (f x-f y)<=L*NX (x-y).

(** Source for [current_lipschitz_lebesgue_action_family_exists]:
    the internally chosen smoothings required by the first
    proof of 4.1.25, p. 383, from the preceding
    4.1.2 and 3.1.6. The sole input is the
    original global Lipschitz bound. The construction supplies
    every approximation and differential-convergence law. *)
Theorem current_lipschitz_lebesgue_action_family_exists :
  exists g:nat->X->Y, is_current_lipschitz_lebesgue_action_family f L g.
Proof.
have hContinuous : norm_class_zero NX NY setT f.
  apply:(@euclidean_lipschitz_norm_class_zero R m n f).
  apply:metric_lipschitz_of_bound.
  split; first exact:hL.
  by move=>x y _ _; exact:hLip x y.
have hExists e : exists ge:X->Y,
    0<e -> is_smoothing_convolution hNY (family e) f ge.
  case:(pselect (0<e))=>he.
  - have [ge hGe] := @continuous_compact_convolution_exists R m Y NY hNY
      (@euclidean_own_norm_complete R n) f hContinuous (family e)
      (@smoothing_dilation_smooth R m phi hPhi family hFamily e he)
      e (@smoothing_dilation_zero_beyond_radius R m phi family hPhi hFamily e he).
    by exists ge.
  - exists f; by move=>he'; contradiction.
have [G hG] := choice hExists.
have hSmooth e (he:0<e) : norm_class_all_orders hNX hNY setT (G e).
  exact:(@continuous_smooth_convolution_smooth R m Y NY hNY
    (@euclidean_own_norm_complete R n) f hContinuous (family e) e (G e)
    (@smoothing_dilation_smooth R m phi hPhi family hFamily e he)
    (@smoothing_dilation_zero_beyond_radius R m phi family hPhi hFamily e he)
    (@hG e he)).
have hLipG e (he:0<e) x y : NY (G e x-G e y)<=L*NX (x-y).
  exact:(@smoothing_lipschitz_bound R m Y NY hNY phi hPhi family hFamily
    e f (G e) L he (@hG e he) hLip x y).
have hError e (he:0<e) x : NY (G e x-f x)<=L*e.
  exact:(@smoothing_lipschitz_error_bound R m Y NY hNY
    (@euclidean_own_norm_complete R n) phi hPhi family hFamily
    e f (G e) L he hL (@hG e he) hLip x).
pose epsilon (i:nat):R := ((i.+1)%:R:R)^-1.
have hPositive i : 0<epsilon i by rewrite /epsilon invr_gt0 ltr0n.
have hSmall d (hd:0<d) : exists N:nat, forall i:nat,
    (N<=i)%N -> epsilon i<d.
  have [N hN] := @extended_finite_order_limit_error R
    (fun i:nat=>((i.+1)%:R:R)^-1) 0 d
    (@reciprocal_natural_order_limit R) hd.
  exists N=>i hi.
  have hBound := hN i hi.
  by rewrite subr0 (ger0_norm (ltW (hPositive i))) in hBound.
pose g i := G (epsilon i).
exists g; constructor.
- exact:hL.
- move=>i; exact:hSmooth (hPositive i).
- move=>i; exact:hLipG (hPositive i).
- move=>i x.
  apply:hom_operator_norm_least; first exact:hL.
  have hActual := @current_map_differential_actual R m n setT
    (g i) (@hSmooth (epsilon i) (hPositive i)) x Logic.I.
  exact:(@norm_differential_global_lipschitz_bound R X Y NX NY hNX hNY
    (g i) x (@current_map_differential R m n setT (g i) x) L
    hActual (@hLipG (epsilon i) (hPositive i))).
- move=>eta hEta.
  have hLarge : 0<L+1 := ltr_wpDl hL ltr01.
  have hScaled : 0<eta/(L+1) by rewrite divr_gt0.
  have [N hN] := hSmall (eta/(L+1)) hScaled.
  exists N=>i hi x.
  apply:le_lt_trans (@hError (epsilon i) (hPositive i) x) _.
  have hLL : L <= L+1 by rewrite lerDl.
  apply:le_lt_trans (ler_wpM2r (ltW (hPositive i)) hLL) _.
  have hBound := @hN i hi.
  have hProduct : (L+1)*epsilon i < (L+1)*(eta/(L+1)).
    by rewrite ltr_pM2l.
  by rewrite [X in _ < X]mulrC divfK ?(lt0r_neq0 hLarge) in hProduct.
- have hAE := @current_lipschitz_lebesgue_action_smoothing_differential_ae
    R m n f L hL hLip phi hPhi family hFamily G hG.
  apply:(@measure_almost_everywhere_mono R X (@euclidean_lebesgue_measure R m)
    (euclidean_lebesgue_is_measure R m) _ _ _ hAE)=>x hx D hD eta hEta.
  have [delta [hDelta hBound]] := hx D hD eta hEta.
  have [N hN] := hSmall delta hDelta.
  exists N=>i hi; exact:hBound (epsilon i) (hPositive i) (hN i hi).
Qed.
End LebesgueActionFamilyExistence.
