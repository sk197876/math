(** Federer (1969), 2.10.24, pp. 186–187: supporting comparison of the
    weighted infimum with a countable nonnegative characteristic expansion.
    Cover each finite-mass level set at increasingly fine positive cutoffs,
    with summable cost errors, then assemble the rows while keeping all
    final weights finite. This supplies the upper-integral inequality
    without assuming countable subadditivity of a fixed-cutoff weighted
    infimum. Source context: WeightedMetricEnvelopeUP.v; assembly details:
    FineWeightedCoverAssembly.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets cardinality reals constructive_ereal topology lra.
From Federer Require Import WeightedMetricEnvelopeUP WeightedCoverCutoffs WeightedCoverScale FineWeightedCoverAssembly
  CaratheodoryLimitUP CaratheodoryLimitMeasure MetricScaleEnvelopeUP MetricScaleEnvelope MetricScaleApproximation
  MeasureUP MeasureBasic MeasureAlmostUP MeasureAlmostBasic NonnegativeSum NonnegativeSumAdd
  NonnegativeSumScale GeometricErrorBudget ExtendedScaledErrorBound MetricDiameter.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [weighted_level_sum]: supporting
    nonnegative characteristic expansion used to compare
    lambda_delta with the upper integral in
    2.10.24, p. 187. Only the levels
    containing x contribute. *)
Definition weighted_level_sum (R : realType) (X : choiceType)
    (A : nat -> set X) (w : nat -> R) (x : X) :=
  nonnegative_sum setT (fun n=>if x \in A n then (w n)%:E else 0).

(** Source for [weighted_metric_envelope_level_bound]: supporting
    countable level-cover bound for the general
    upper-integral inequality in 2.10.24,
    p. 187. Each chosen level set has
    finite final mass and the total level cost
    is finite; measurability of f and the
    individual level sets is not needed here. *)
Theorem weighted_metric_envelope_level_bound (R : realType) (X : metricType R) (J : choiceType)
    (S : J -> set X) (c : J -> \bar R) (psi : set X -> \bar R) (delta : \bar R)
    (lambda : (X -> \bar R) -> \bar R) (f : X -> \bar R)
    (A : nat -> set X) (w : nat -> R) :
  is_caratheodory_limit S c psi -> (forall j, 0<=c j) -> 0<delta ->
  is_weighted_metric_envelope S c psi delta lambda ->
  (forall n, (0<=w n)%R) -> (forall n, psi (A n)< +oo) ->
  nonnegative_sum setT (fun n=>(w n)%:E*psi (A n))< +oo ->
  measure_almost_everywhere psi [set x | f x<=weighted_level_sum A w x] ->
  lambda f<=nonnegative_sum setT (fun n=>(w n)%:E*psi (A n)).
Proof.
move=> hpsi hc hd hl hw hA hfinite hdom.
have hm := caratheodory_limit_is_measure hpsi hc.
pose M := nonnegative_sum setT (fun n=>(w n)%:E*psi (A n)).
have hM0 : 0<=M := nonnegative_sum_nonnegative _ _.
have hMfin : M \is a fin_num by rewrite (ge0_fin_numE hM0).
pose p := fine M.
have hM : M=p%:E by rewrite /p fineK.
change (lambda f<=M); rewrite hM.
have [r [hr hfine]] := positive_cofinal_metric_cutoffs hd.
apply: (@extended_upper_bound_from_scaled_errors R (lambda f) p 1%R (@ler01 R))=> e he.
pose b n := geometric_error_budget e n.
have hb n : (0<b n)%R := geometric_error_budget_positive n he.
pose t n := (b n/(w n+1))%R.
have hw1 n : (0<w n+1)%R by have hh := hw n; lra.
have ht n : (0<t n)%R := divr_gt0 (hb n) (hw1 n).
have hcost n : (w n*t n<=b n)%R.
  have hle : (w n<=w n+1)%R by lra.
  have hh := ler_wpM2r (ltW (ht n)) hle.
  have hne : (w n+1!=0)%R by rewrite gt_eqF.
  have heq : ((w n+1)*t n=b n)%R by rewrite mulrC /t divfK.
  by rewrite heq in hh.
pose nu n := metric_scale_envelope S c (r n)%:E.
have hnu n := @metric_scale_envelope_specification R X J S c (r n)%:E.
have hrE n : 0<(r n)%:E by rewrite lte_fin; exact: (hr n).1.
have hnear n : nu n (A n)<psi (A n)+(t n)%:E.
  have hbound := @caratheodory_limit_upper R X J S c psi hpsi (A n) (r n)%:E (nu n) (hrE n) (hnu n).
  have hfin : psi (A n) \is a fin_num.
    rewrite ge0_fin_numE; last exact: (@measure_nonnegative R X psi hm (A n)).
    exact: hA n.
  apply: le_lt_trans hbound _.
  rewrite -{1}[psi (A n)]adde0 lteD2lE // lte_fin; exact: ht n.
have hex n := metric_scale_envelope_approximation (hnu n) (hnear n).
pose G n := projT1 (cid (hex n)).
have hG n : countable (G n) /\
    (forall j, G n j -> extended_metric_diameter (S j)<=(r n)%:E) /\
    A n `<=` \bigcup_(j in G n) S j /\ nonnegative_sum (G n) c<psi (A n)+(t n)%:E :=
  projT2 (cid (hex n)).
pose a n := fun _ : J=>w n.
have hrow n : weighted_generator_cost c (G n) (a n)<=(w n)%:E*psi (A n)+(b n)%:E.
  rewrite /weighted_generator_cost /a (@nonnegative_sum_scale R J (G n) c (w n) (hw n) (fun j _=>hc j)).
  have hwE : 0<=(w n)%:E by rewrite lee_fin; exact: hw.
  have hmul := lee_wpmul2l hwE (ltW (hG n).2.2.2).
  have hfin : psi (A n) \is a fin_num by rewrite (ge0_fin_numE (measure_nonnegative hm (A n))); exact: hA n.
  have hval : psi (A n)=(fine (psi (A n)))%:E by rewrite fineK.
  apply: le_trans hmul _; rewrite hval -EFinD -!EFinM -EFinD lee_fin.
  have hh := hcost n; by rewrite mulrDr; exact: lerD (lexx _) hh.
pose T := nonnegative_sum setT (fun n=>weighted_generator_cost c (G n) (a n)).
have hT : T<=M+(e/2)%:E.
  have hh : T<=nonnegative_sum setT (fun n=>(w n)%:E*psi (A n)+(b n)%:E).
    apply: nonnegative_sum_mono=> n _; exact: hrow.
  rewrite nonnegative_sum_add in hh; last 2 first.
  - move=> n _; apply: mule_ge0; [by rewrite lee_fin; exact: hw|exact: (@measure_nonnegative R X psi hm (A n))].
  - by move=> n _; rewrite lee_fin; exact: ltW (hb n).
  apply: le_trans hh _; apply: leeD; first exact: lexx _.
  exact: geometric_error_sum_bound he.
have hTfinite : T< +oo.
  apply: le_lt_trans hT _; by rewrite hM -EFinD ltry.
have hdiam n j (hj : G n j) : extended_metric_diameter (S j)<=delta :=
  le_trans ((hG n).2.1 j hj) (hr n).2.
have hfineG q (hq : (0<q)%R) : exists N, forall n j, (N<=n)%N -> G n j -> extended_metric_diameter (S j)<=q%:E.
  have [N hN] := hfine q hq; exists N=> n j hn hj.
  apply: le_trans ((hG n).2.1 j hj) _; rewrite lee_fin; exact: hN n hn.
have hdomG : measure_almost_everywhere psi [set x | f x<=nonnegative_sum setT (fun n=>weighted_generator_sum S (G n) (a n) x)].
  apply: (@measure_almost_everywhere_mono R X psi hm _ _ _ hdom)=> x hx.
  apply: le_trans hx _; apply: nonnegative_sum_mono=> n _.
  case hn: (x \in A n).
  - have hxA : A n x := set_mem hn.
    have [j hj hxj] := (hG n).2.2.1 x hxA.
    exact: (@weighted_generator_sum_member_bound R X J S (G n) (a n) j x hj hxj).
  - exact: nonnegative_sum_nonnegative.
have [H [u [hcover hbudget]]] := @fine_weighted_cover_assembly R X J S c psi delta f G a
  hpsi hc (fun n=>(hG n).1) (fun n j hj=>hw n) hdiam hfineG hTfinite hdomG.
have hh := le_trans (weighted_metric_envelope_lower hl hcover) (le_trans hbudget hT).
rewrite hM -EFinD in hh.
apply: le_trans hh _; rewrite mul1r lee_fin.
have he2 : (e/2<=e)%R by lra.
exact: lerD (lexx p) he2.
Qed.
