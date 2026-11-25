(** Federer (1969), 4.1.14, p. 371: pass the smooth
    affine-chain mass bounds to the original weak limit.
    The weights converge uniformly only on the compact
    carrying set of the original finite variation. The
    preceding mass lower semicontinuity supplies the limit. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals constructive_ereal topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  CurrentSpaces CurrentMassSealed CurrentMassWeakLowerLimit
  CurrentWeakSequenceLimit MeasureUP RadonMeasureUP MeasureIntegralUP
  MeasureIntegralBounds MeasureIntegralUniqueness SummableRealFunctionUP
  CompactCarriedContinuousIntegral.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section CurrentWeightedApproximationMassLimit.
Variable R : realType.
Hypothesis h2 : (1+1:R)!=0.
Variables nu j : nat.
Variable V : set (R_n R nu).
Hypothesis hV : forall y, V y -> norm_domain_interior
  (inner_norm (@euclidean_inner_productP R nu)) V y.
Local Notation C := (@current_space R h2 nu V hV j).
Local Notation M := (@CurrentMass.value R h2 nu j V hV).
Variables (P : nat -> C) (Q : C).
Hypothesis hWeak : @is_current_weak_sequence_limit R h2 nu j V hV P Q.

(** Source for [current_mass_weak_convergent_bounds]: the original
    mass lower semicontinuity of 4.1.5, p. 350, passes
    a convergent sequence of finite upper bounds to the
    weak limit in Federer 4.1.14, p. 371. No finite-mass
    or representation premise is imposed on that limit. *)
Theorem current_mass_weak_convergent_bounds (a : nat -> R) (b : R) :
  (forall i, (M (P i)<=(a i)%:E)%E) ->
  (forall eps:R, 0<eps -> exists N:nat, forall i:nat,
    (N<=i)%N -> `|a i-b|<eps) ->
  (M Q<=b%:E)%E.
Proof.
move=> hBound hLimit.
apply/lee_addgt0Pr=> eps hEps.
have [N hN] := hLimit eps hEps.
apply: (@current_mass_weak_closed_bound R h2 nu j V hV P Q
  (b%:E+eps%:E)%E N hWeak).
move=> i hi.
apply: (le_trans (hBound i)).
rewrite -EFinD lee_fin.
have hError : a i-b<=eps := le_trans (ler_norm _) (ltW (hN i hi)).
by rewrite lerBlDr addrC in hError.
Qed.

Variable X : metricType R.
Variable mu : set X -> \bar R.
Hypotheses (hm : is_measure mu) (hr : is_radon_measure mu).
Variable mass : R.
Hypothesis hMass : mu setT=mass%:E.
Variable K : set X.
Hypotheses (hK : compact K) (hCarried : mu (~` K)=0).

(** Source for [current_weighted_approximation_mass_limit]: the
    exact smooth approximation integrals converge on the
    original compact-carried variation, so their original
    current mass bounds imply the printed affine inequality
    of Federer 4.1.14, p. 371. The integral witness b
    is an actual integral, not a postulated chosen value. *)
Theorem current_weighted_approximation_mass_limit
    (w : nat -> X -> R^o) (v : X -> R^o) (b : R) :
  (forall i, continuous (w i)) ->
  is_measure_integral mu (real_total_integrand v) b%:E ->
  (forall eps:R, 0<eps -> exists N:nat, forall i:nat, (N<=i)%N ->
    forall x, K x -> `|w i x-v x|<eps) ->
  (forall i, (M (P i)<=measure_lower_integral mu
    (real_total_integrand (w i)))%E) ->
  (M Q<=b%:E)%E.
Proof.
move=> hW hVIntegral hUniform hBound.
have [a [hA hLimit]] := @compact_carried_continuous_integral_limit
  R X mu hm hr mass hMass K hK hCarried w v b hW hVIntegral hUniform.
apply: (@current_mass_weak_convergent_bounds a b _ hLimit)=> i.
have hValue := @measure_lower_integral_unique R X mu _ _ _
  (measure_lower_integral_specification mu (real_total_integrand (w i)))
  (hA i).2.2.
by rewrite -hValue; exact: hBound.
Qed.
End CurrentWeightedApproximationMassLimit.
