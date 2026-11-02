(** Federer (1969), 2.5.7, p. 98: increasing-sequence closure of the
    dominated density family U, with a real representative of the almost
    finite limit. The last domination inequality below uses the already
    proved Fatou inequality; this suffices for the upper bound obtained by
    the printed monotone convergence argument. All products are proved
    summable by Holder before their sealed integral values are used. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import PartialFunctionUP MeasureUP MeasureAlmostUP MeasureAlmostBasic
  PartialExtendedOrderLoci PartialDominatedConvergence MeasureIntegralUP MeasureFatouConvergent
  ExtendedRealBoundsUP ExtendedLowerLimitUP ExtendedLowerLimit ExtendedRealOrderLimit RealScalarOrderLimits
  FunctionLatticeUP SummableRealFunctionUP TotalScalarLpUP TotalScalarLpFiniteSeminorm
  TotalScalarPairingValue TotalLpPairingBound LpConjugatePair LpDominatedDensityFamily
  RealLowerLimitReplacement TotalScalarLpIncreasingLimit.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [positive_pairing_limit_upper_bound]: the limiting
    test-function inequality in Federer 2.5.7, p. 98 The conclusion needs
    only almost-everywhere convergence of the nonnegative densities, since
    Fatou already proves the required one-sided inequality. *)
Lemma positive_pairing_limit_upper_bound (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu) p q
    (u : nat -> X -> R) (k f : X -> R) (C : R) :
  is_lp_conjugate_pair p q ->
  (forall n, total_scalar_lp mu q (u n)) -> total_scalar_lp mu q k ->
  (forall n x, (0 <= u n x)%R) ->
  positive_function_lattice (total_scalar_lp mu p) f ->
  measure_almost_everywhere mu [set x | extended_order_limit (fun n => (u n x)%:E) (k x)%:E] ->
  (forall n, (total_scalar_pairing mu f (u n) <= C)%R) ->
  (total_scalar_pairing mu f k <= C)%R.
Proof.
move=> hpq hu hk hu0 hf hl hb.
have hi n := (@total_lp_pairing_specification_and_bound R X mu hm p q f (u n) hpq hf.1 (hu n)).1.
have hki := (@total_lp_pairing_specification_and_bound R X mu hm p q f k hpq hf.1 hk).1.
have hpos n : measure_almost_everywhere mu
    (partial_extended_nonnegative_locus (real_total_integrand (fun x => (f x*u n x)%R))).
  apply: (@measure_almost_everywhere_mono R X mu hm setT _ _ (measure_almost_everywhere_true hm))=> x _.
  exists (f x*u n x)%:E; split; first by apply/real_total_integrand_graph.
  change (is_true (0 <= f x*u n x)%R); exact: mulr_ge0 (hf.2 x) (hu0 n x).
have hlim : measure_almost_everywhere mu (partial_extended_convergence_locus
    (fun n => real_total_integrand (fun x => (f x*u n x)%R))
    (real_total_integrand (fun x => (f x*k x)%R))).
  apply: (@measure_almost_everywhere_mono R X mu hm _ _ _ hl)=> x hx.
  exists (fun n => (f x*u n x)%:E), (f x*k x)%:E; split.
  - move=> n; by apply/real_total_integrand_graph.
  split; first by apply/real_total_integrand_graph.
  exact: (@real_scalar_order_limit R (fun n => u n x) (k x) (f x) hx).
have hfatou := @measure_fatou_convergent_values R X mu hm _ _ _ _ hlim hpos hi hki.
have hbound : extended_lower_limit (fun n => (total_scalar_pairing mu f (u n))%:E) <= C%:E.
  apply: (extended_real_supremum_least (extended_lower_limit_laws _))=> b [K hK].
  apply: le_trans (hK K (leqnn K)) _; rewrite lee_fin; exact: hb K.
have hh := le_trans hfatou hbound; by rewrite lee_fin in hh.
Qed.

(** Source for [lp_dominated_density_increasing_limit]: the actual
    increasing-sequence closure of U in Federer 2.5.7, p. 98 The norm,
    support, and domination conditions are all proved for the
    representative; no closure or existence premise is assumed. *)
Theorem lp_dominated_density_increasing_limit (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu) p q (P : (X -> R) -> R)
    (M : R) (u : nat -> X -> R) :
  is_lp_conjugate_pair p q -> (0 <= M)%R ->
  (forall f, positive_function_lattice (total_scalar_lp mu p) f ->
    (P f <= M*finite_total_scalar_lp_norm mu p f)%R) ->
  (forall n, lp_dominated_density_family mu p q P (u n)) ->
  (forall n m x, (n <= m)%N -> (u n x <= u m x)%R) ->
  lp_dominated_density_family mu p q P (real_lower_limit_replacement u) /\
  total_scalar_lp_norm mu q (real_lower_limit_replacement u) <= M%:E /\
  measure_almost_everywhere mu [set x | extended_increases_to
    (fun n => (u n x)%:E) (real_lower_limit_replacement u x)%:E].
Proof.
move=> hpq hM hP hu hinc.
have hb n := @lp_dominated_density_norm_bound R X mu hm p q P (u n) M hpq hM hP (hu n).
have [hk [hk0 [hkbound hl]]] := @bounded_increasing_lp_replacement R X mu hm q M u
  (fun n => (hu n).1) (fun n => (hu n).2.1) hinc hb.
split; last by split.
split=> //; split=> //; move=> f hf.
apply: (@positive_pairing_limit_upper_bound R X mu hm p q u _ f (P f)
  hpq (fun n => (hu n).1) hk (fun n => (hu n).2.1) hf).
- apply: (@measure_almost_everywhere_mono R X mu hm _ _ _ hl)=> x hx; exact: hx.2.
- move=> n; exact: (hu n).2.2 f hf.
Qed.
