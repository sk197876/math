(** Federer (1969), 2.3.9, p. 79: completeness yields a pointwise limit when
    successive distances have a finite sum. The limit retains the
    quantitative tail bound. This is the supporting metric argument in the
    last paragraph. Source context: SummableMetricIncrementBound.v. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets
  reals constructive_ereal topology.
From Federer Require Import NonnegativeSum NonnegativeSequenceTail
  SummableMetricIncrementBound CompleteMetricUP MetricClosedBalls.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [summable_metric_increment_limit]: supporting
    Cauchy-sequence and closed-ball argument for Federer 2.3.9,
    p. 79. Only completeness of the metric space is required;
    the normed-space structure enters later when applying it. *)
Theorem summable_metric_increment_limit (R : realType) (T : metricType R)
    (hT : is_complete_metric_space T) (u : nat -> T) (a : nat -> \bar R) j :
  (forall n, 0 <= a n) -> nonnegative_sum setT a < +oo ->
  (forall n, (j <= n)%N -> (mdist (u n.+1) (u n))%:E <= a n) ->
  exists z, u @ \oo --> z /\ forall m, (j <= m)%N ->
    (mdist z (u m))%:E <= nonnegative_sequence_tail a m.
Proof.
move=> ha hf hinc.
have hb := @summable_metric_increment_bound R T u a j ha hinc.
have PF0 : ProperFilter (\oo : set_system nat) by typeclasses eauto.
have PF : ProperFilter (u @ \oo) := @fmap_proper_filter nat T u \oo PF0.
have hc : cauchy (u @ \oo).
  apply: cauchy_exP=> e he.
  have [K hK] := nonnegative_sequence_tail_small ha hf he.
  pose k := maxn j K.
  exists (u k); exists k=> // n hn.
  rewrite ballEmdist /= (metric_sym (u k)).
  have hh := le_lt_trans (hb k n (leq_maxl _ _) hn) (hK k (leq_maxr _ _)).
  by move: hh; rewrite lte_fin.
have [z hz] := hT _ PF hc; exists z; split=> // m hjm.
have hfin := nonnegative_sequence_tail_finite hf m.
have hevent : \forall n \near \oo,
    metric_closed_ball (u m) (fine (nonnegative_sequence_tail a m)) (u n).
  exists m=> // n hn.
  have hh := hb m n hjm hn.
  rewrite -(fineK hfin) lee_fin (metric_sym (u n)) in hh; exact hh.
have hzball := @closed_cvg nat T \oo PF0 u
  (metric_closed_ball (u m) (fine (nonnegative_sequence_tail a m)))
  (@metric_closed_ball_closed R T (u m) (fine (nonnegative_sequence_tail a m))) hevent z hz.
by rewrite -(fineK hfin) lee_fin metric_sym; exact hzball.
Qed.
