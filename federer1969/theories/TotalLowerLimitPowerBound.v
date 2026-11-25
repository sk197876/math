(** Federer (1969), 2.5.7, p. 98: Fatou bounds the integral of the qth power
    of the candidate limit, making that limit finite almost everywhere. This
    supporting theorem is stated with actual uniformly bounded power
    integrals; the Lq specialization supplies them from the norm laws. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import ExtendedRealOrderTopology PartialFunctionUP PartialFunctionBasic PartialExtendedOrderLoci
  MeasureUP MeasureAlmostUP MeasureAlmostBasic MeasureIntegralUP MeasureIntegralBounds
  MeasureLowerLimitNonnegative MeasureFatou MeasureSummableFiniteValues ExtendedRealBoundsUP
  ExtendedLowerLimitUP ExtendedLowerLimit ExtendedPositivePower TotalExtendedLowerLimit TotalLowerLimitPower.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [total_lower_limit_power_integral_bound]: supporting Fatou
    estimate in Federer 2.5.7, p. 98 The initial extended limit is retained,
    and its finite power integral is established. *)
Theorem total_lower_limit_power_integral_bound (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu)
    (f : nat -> X -> extended_real_line R) (p : R) (a : nat -> R) (C : R) :
  (forall n x, 0 <= f n x) -> (0 < p)%R ->
  (forall n, is_measure_integral mu
    (partial_function_total (fun x => (extended_positive_power (f n x) p : extended_real_line R))) (a n)%:E) ->
  (forall n, (a n <= C)%R) ->
  exists b : R, (0 <= b <= C)%R /\ is_measure_integral mu
    (partial_function_total (fun x => (extended_positive_power (total_extended_lower_limit f x) p : extended_real_line R))) b%:E.
Proof.
move=> hf hp hi hC.
pose F n := partial_function_total (fun x => (extended_positive_power (f n x) p : extended_real_line R)).
pose G := partial_function_total (fun x => (extended_positive_power (total_extended_lower_limit f x) p : extended_real_line R)).
have hl := @total_lower_limit_power_specification R X f p hf hp.
have hpos n : measure_almost_everywhere mu (partial_extended_nonnegative_locus (F n)).
  apply: (@measure_almost_everywhere_mono R X mu hm setT _ _ (measure_almost_everywhere_true hm))=> x _.
  exists (extended_positive_power (f n x) p); split=> //; exact: extended_positive_power_nonnegative.
have [hgi hg0] := @measure_lower_limit_nonnegative_integral R X mu hm F G hl (fun n => (hi n).1) hpos.
have hb := @measure_fatou_integral_values R X mu hm F G (fun n => (a n)%:E) _ hl hpos hi hgi.
have hbound : extended_lower_limit (fun n => (a n)%:E) <= C%:E.
  apply: (extended_real_supremum_least (extended_lower_limit_laws _))=> d [K hK].
  apply: le_trans (hK K (leqnn K)) _; rewrite lee_fin; exact: hC K.
have hG : measure_lower_integral mu G <= C%:E := le_trans hb hbound.
have hfin : measure_lower_integral mu G \is a fin_num.
  rewrite (ge0_fin_numE hg0); exact: le_lt_trans hG (ltry C).
exists (fine (measure_lower_integral mu G)); split.
- apply/andP; split; first exact: fine_ge0 hg0.
  by rewrite -(fineK hfin) lee_fin in hG.
- by rewrite fineK.
Qed.

(** Source for [total_lower_limit_power_almost_finite]: almost finiteness of
    the candidate limit from bounded positive-power integrals in Federer
    2.5.7, p. 98 Infinite values are excluded by a proof, before any
    real-valued replacement is used. *)
Theorem total_lower_limit_power_almost_finite (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu)
    (f : nat -> X -> extended_real_line R) (p : R) (a : nat -> R) (C : R) :
  (forall n x, 0 <= f n x) -> (0 < p)%R ->
  (forall n, is_measure_integral mu
    (partial_function_total (fun x => (extended_positive_power (f n x) p : extended_real_line R))) (a n)%:E) ->
  (forall n, (a n <= C)%R) ->
  measure_almost_everywhere mu [set x | total_extended_lower_limit f x \is a fin_num].
Proof.
move=> hf hp hi hC.
have [b [_ hbi]] := @total_lower_limit_power_integral_bound R X mu hm f p a C hf hp hi hC.
have hfinite := @measure_summable_finite_almost R X mu hm _ (ex_intro _ b hbi).
apply: (@measure_almost_everywhere_mono R X mu hm _ _ _ hfinite)=> x [y [hy hyfin]].
have he : extended_positive_power (total_extended_lower_limit f x) p=y := hy.
have h0 := @total_extended_lower_limit_nonnegative R X f hf x.
change (is_true (total_extended_lower_limit f x \is a fin_num)).
rewrite (ge0_fin_numE h0) -(extended_positive_power_finite_iff h0 hp) he.
by move: hyfin; rewrite fin_numElt=> /andP [_ hlt].
Qed.
