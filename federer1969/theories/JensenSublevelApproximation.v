(** Federer (1969), 2.4.19, p. 91: exhaustion by the closed convex sets C_n.
    We use a cofinal sequence of thresholds containing a fixed c in C, and
    put c outside each inverse-image set. This is an equivalent
    implementation of the printed restriction argument: the source measure
    and its normalising mass stay fixed, while the additional constant
    contributions vanish on the shrinking complement. The convergence proof
    uses the majorant |g-c|. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric RealMetricBackground MetricSubsetBackground
  PartialFunctionUP PartialFunctionBasic PartialFunctionLimitUP MeasureUP MeasureAlmostUP MeasureAlmostBasic
  MeasurableFunctionBorel TopologicalBorel MeasurableNormedBasic MeasurableNormedPiecewise
  MeasureLpMembershipUP MeasureLpConvergence ConvexFunctionUP ConvexClosedSublevels
  MeasureReferenceDominatedLpConvergence PointwiseEventuallyConstant.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [jensen_threshold_left_bound]: supporting cofinal threshold
    choice for the C_n of Federer 2.4.19, p. 91 *)
Lemma jensen_threshold_left_bound (R : realType) (a b : R) : (a <= Order.max a b)%R.
Proof. by rewrite le_max lexx. Qed.

(** Source for [jensen_threshold_right_bound]: supporting cofinal threshold
    choice for the C_n of Federer 2.4.19, p. 91 *)
Lemma jensen_threshold_right_bound (R : realType) (a b : R) : (b <= Order.max a b)%R.
Proof. by rewrite le_max lexx orbT. Qed.

(** Source for [jensen_sublevel_approximation]: supporting bounded-range
    exhaustion of g in Federer 2.4.19, p. 91 The mean correction from
    filling the complement with c tends to zero in L1. The scalar bound is
    retained for the subsequent integral limit. *)
Theorem jensen_sublevel_approximation (R : realType) (X : choiceType)
    (V : lmodType R) (N : V -> R) (hN : is_real_norm N)
    (mu : set X -> \bar R) (hm : is_measure mu) (m : R)
    (C : set (real_norm_metric_space hN)) (c : real_norm_metric_space hN)
    (F : real_norm_metric_space hN -> real_line_metric R) (g : X -> real_norm_metric_space hN) :
  mu setT=m%:E -> closed C -> is_real_convex_function_on C F ->
  continuous (fun y : metric_subset C => F (val y)) -> C c ->
  (forall y, C y -> (0 <= F y)%R) -> (forall x, C (g x)) ->
  is_measure_lp_function mu 1%R (partial_function_total g) ->
  exists (t : nat -> R) (f : nat -> X -> real_norm_metric_space hN),
    (forall n, jensen_closed_sublevel N C F (t n) c) /\
    (forall n x, jensen_closed_sublevel N C F (t n) (f n x)) /\
    (forall n, is_measure_lp_function mu 1%R (partial_function_total (f n))) /\
    (forall x, (fun n => f n x) @ \oo --> g x) /\
    converges_in_lp_norm mu N 1%R (fun n => partial_function_total (f n)) (partial_function_total g) /\
    (forall n x, (F (f n x) <= F (g x)+F c)%R).
Proof.
move=> hmass hC hconv hF hc hpos hgC hg.
pose b := (Order.max (N c) (F c))%R.
have hb0 : (0 <= b)%R := le_trans (real_seminorm_nonnegative hN.1 c) (jensen_threshold_left_bound _ _).
pose t n := (b+n%:R)%R.
pose D n : set (real_norm_metric_space hN) := jensen_closed_sublevel N C F (t n).
have hcD n : D n c.
  have hbt : (b <= t n)%R by rewrite /t lerDl ler0n.
  split=> //; split.
  - exact: (le_trans (jensen_threshold_left_bound _ _) hbt).
  - exact: (le_trans (jensen_threshold_right_bound _ _) hbt).
have hD n := @jensen_sublevel_closed_convex R V N hN C F (t n) hC hconv hF.
pose A n := [set x | D n (g x)].
have hA n : measure_measurable mu (A n).
  have hh := @measurable_function_borel_preimage R X (real_norm_metric_space hN) mu hm
    (partial_function_total g) hg.2.1.1 (D n) (closed_borel_set (hD n).1).
  have he : partial_function_preimage (partial_function_total g) (D n)=A n.
    apply/seteqP; split=> x; first by move=> [y [hy hdy]]; rewrite -(hy : g x=y) in hdy.
    by move=> hx; exists (g x); split.
  by rewrite he in hh.
pose f n x := if pselect (A n x) then g x else c.
have hfD n x : D n (f n x).
  rewrite /f; case: (pselect (A n x))=> hx; [exact hx|exact: hcD].
have hfme n := @measurable_normed_total_piecewise R X V N hN mu hm (A n) g (fun _ => c)
  (hA n) hg.2.1 (@measurable_normed_total_constant R X V N hN mu hm c).
have hevent x : exists K, forall n, (K <= n)%N -> f n x=g x.
  pose K := Num.bound (Order.max (N (g x)) (F (g x)))%R.
  have hK : (Order.max (N (g x)) (F (g x)) < K%:R)%R.
    apply: archi_boundP; exact: (le_trans (real_seminorm_nonnegative hN.1 _) (jensen_threshold_left_bound _ _)).
  exists K=> n hn.
  have hkn : (K%:R <= n%:R :> R)%R by rewrite ler_nat.
  have hnt : (n%:R <= t n)%R by rewrite /t lerDr.
  have hh := le_trans (ltW hK) (le_trans hkn hnt).
  have hAn : A n x.
    split; first exact: hgC.
    split; [exact: le_trans (jensen_threshold_left_bound _ _) hh|exact: le_trans (jensen_threshold_right_bound _ _) hh].
  by rewrite /f; case: (pselect (A n x))=> // h; exact: False_ind (h hAn).
have hlim := pointwise_eventually_equal_limit hevent.
have hl : measure_almost_everywhere mu (partial_function_limit_locus
    (fun n => partial_function_total (f n)) (partial_function_total g)).
  apply: (@measure_almost_everywhere_mono R X mu hm setT _ _ (measure_almost_everywhere_true hm))=> x _.
  exists (fun n => f n x),(g x); by split=> //; split.
have herr n : measure_almost_everywhere mu [set x | (N (g x-f n x) <= N (g x-c))%R].
  apply: (@measure_almost_everywhere_mono R X mu hm setT _ _ (measure_almost_everywhere_true hm))=> x _.
  change (is_true (N (g x-f n x) <= N (g x-c))%R).
  rewrite /f; case: (pselect (A n x))=> hx; last exact: lexx.
  rewrite subrr (real_seminorm_zero hN.1); exact: real_seminorm_nonnegative hN.1 _.
have [hflp hflim] := @measure_reference_dominated_lp_one_convergence R X V N hN mu hm m g c f
  hmass hg hfme hl herr.
exists t,f; split=> //; split=> //; split=> //; split=> //; split=> // n x.
rewrite /f; case: (pselect (A n x))=> hx.
- by rewrite lerDl; exact: hpos.
- by rewrite lerDr; exact: hpos (hgC x).
Qed.
