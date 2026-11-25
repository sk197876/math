(** Federer (1969), 2.10.24, pp. 186–187: supporting assembly of
    increasingly fine weighted covers while retaining finite real weights.
    Repeated occurrences are grouped by generator. An infinite aggregate
    weight can occur only on a zero-diameter, zero-cost generator when the
    total cost is finite; such generators have zero final mass. This expands
    the countable-cover choices without changing the printed weight domain.
    Source context: WeightedMetricEnvelopeUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra finmap boolp classical_sets reals constructive_ereal topology.
From Federer Require Import NonnegativeSum NonnegativeSumSupport NonnegativeSumExtendedScale MetricDiameterUP MetricDiameter
  ExtendedScaledErrorBound.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [repeated_generator_weight]: supporting
    grouped weight for repeated generators in the
    weighted-cover proof of 2.10.24, pp. 186–187.
    It is an extended sum used to prove that
    the final chosen weights are real-valued. *)
Definition repeated_generator_weight (R : realType) (J : choiceType)
    (G : nat -> set J) (a : nat -> J -> R) (j : J) :=
  nonnegative_sum [set n | G n j] (fun n=>(a n j)%:E).

(** Source for [infinite_repeated_weight_late_member]: supporting
    finite-prefix observation for 2.10.24,
    pp. 186–187: infinitely large aggregate
    weight requires occurrences at arbitrarily late indices,
    since every individual weight is finite. *)
Lemma infinite_repeated_weight_late_member (R : realType) (J : choiceType)
    (G : nat -> set J) (a : nat -> J -> R) j :
  repeated_generator_weight G a j=+oo -> forall N, exists n, (N<=n)%N /\ G n j.
Proof.
move=> hinf N; apply: contrapT=> hnone.
pose F : {fset nat} := seq_fset tt (iota 0 N).
have hsub : [set n | G n j] `<=` [set` F].
  move=> n hn; change (is_true (n \in F)); rewrite /F seq_fsetE mem_iota add0n leq0n /=.
  rewrite ltnNge; apply/negP=> hNn; apply: hnone; exists n; by split.
have hnorm : nonnegative_sum [set n | G n j] (fun n=>(a n j)%:E)<=
    nonnegative_sum [set n | G n j] (fun n=>(`|a n j|)%:E).
  apply: nonnegative_sum_mono=> n hn; rewrite lee_fin; exact: ler_norm.
have hb := le_trans hnorm (nonnegative_sum_subset (fun n=>(`|a n j|)%:E) hsub).
rewrite nonnegative_sum_finite in hb; last by move=> n hn; rewrite lee_fin; exact: normr_ge0.
rewrite sumEFin in hb; change (nonnegative_sum [set n | G n j] (fun n=>(a n j)%:E)=+oo) in hinf.
rewrite hinf in hb.
have hh := le_lt_trans hb (ltry (\sum_(n <- F) `|a n j|)%R); by rewrite ltxx in hh.
Qed.

(** Source for [infinite_repeated_weight_zero_diameter]: supporting
    removal of infinite aggregate weights in
    2.10.24, pp. 186–187. A generator
    occurring arbitrarily late in increasingly fine
    covers has diameter zero. *)
Lemma infinite_repeated_weight_zero_diameter (R : realType) (X : metricType R) (J : choiceType)
    (S : J -> set X) (G : nat -> set J) (a : nat -> J -> R) j :
  (forall e : R, (0<e)%R -> exists N, forall n k, (N<=n)%N -> G n k -> extended_metric_diameter (S k)<=e%:E) ->
  repeated_generator_weight G a j=+oo -> extended_metric_diameter (S j)=0.
Proof.
move=> hfine hinf.
have h0 := metric_diameter_nonnegative (extended_metric_diameter_specification (S j)).
have hle : extended_metric_diameter (S j)<=0.
  apply: (@extended_upper_bound_from_scaled_errors R _ 0%R 1%R (@ler01 R))=> e he.
  have [N hN] := hfine e he.
  have [n [hNn hnj]] := @infinite_repeated_weight_late_member R J G a j hinf N.
  rewrite mul1r add0r; exact: hN n j hNn hnj.
apply/eqP; by rewrite eq_le hle h0.
Qed.

(** Source for [infinite_repeated_weight_zero_cost]: supporting
    finite-budget observation for assembling the covers
    in 2.10.24, pp. 186–187. Positive
    cost times an infinite aggregate weight contradicts
    the finite total source cost; zero times
    infinity keeps its original nonnegative convention. *)
Lemma infinite_repeated_weight_zero_cost (R : realType) (J : choiceType)
    (G : nat -> set J) (a : nat -> J -> R) (c : J -> \bar R) j :
  (forall n k, G n k -> (0<=a n k)%R) -> (forall k, 0<=c k) ->
  nonnegative_sum setT (fun n=>nonnegative_sum (G n) (fun k=>(a n k)%:E*c k))< +oo ->
  repeated_generator_weight G a j=+oo -> c j=0.
Proof.
move=> ha hc hfinite hinf.
have hscale : nonnegative_sum [set n | G n j] (fun n=>(a n j)%:E*c j)=
    repeated_generator_weight G a j*c j.
  have he : nonnegative_sum [set n | G n j] (fun n=>(a n j)%:E*c j)=
      nonnegative_sum [set n | G n j] (fun n=>c j*(a n j)%:E).
    apply: nonnegative_sum_ext=> n hn; exact: muleC.
  rewrite he nonnegative_sum_extended_scale; [exact: muleC|exact: hc|].
  by move=> n hn; rewrite lee_fin; exact: ha n j hn.
have hcost := nonnegative_sum_mono (fun n (hn : G n j)=>
  @nonnegative_sum_term R J (G n) (fun k=>(a n k)%:E*c k) j hn).
have hsub := nonnegative_sum_subset (fun n=>nonnegative_sum (G n) (fun k=>(a n k)%:E*c k))
  (fun n (_ : G n j)=>Logic.I).
have hbound := le_lt_trans (le_trans hcost hsub) hfinite.
rewrite hscale hinf in hbound.
apply/eqP; rewrite eq_le (hc j) andbT.
case: (leP (c j) 0)=> // hpos.
by rewrite (gt0_mulye hpos) ltxx in hbound.
Qed.
