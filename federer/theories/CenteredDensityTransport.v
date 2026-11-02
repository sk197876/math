(** Federer (1969), 3.1.4, p. 214: supporting identification of
    the scalar parameter line with the one-dimensional Euclidean factor
    used in 3.1.3. Centered density and approximate limits are invariant
    under measure-preserving isometric coordinate identifications. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology lra.
From Federer Require Import MetricClosedBalls MetricDiameter MetricDiameterUP
  CenteredBallRelations CoveringFamilyUP PartialFunctionUP PartialFunctionPrecomposition
  MeasureUP MeasureBasic MeasureRestriction MeasureSetDensity MeasureDerivates
  CoveringFiniteLimitBounds MeasureRatioComparison CenteredZeroDensityCriterion
  MeasureApproximateLimitUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ring_scope.
Local Open Scope ereal_scope.

(** Source for [centered_zero_density_small_mass]: supporting expansion
    of the density-zero estimates underlying Federer 3.1.3 and the
    scalar quotient argument in 3.1.4, p. 214. The metric form applies
    to scalar and Euclidean presentations of the same line. *)
Theorem centered_zero_density_small_mass (R : realType) (X : metricType R)
    (phi : set X -> \bar R) (A : set X) a :
  is_measure phi ->
  (forall x r, (0<r)%R -> 0<phi (metric_closed_ball x r) /\
    phi (metric_closed_ball x r) \is a fin_num) ->
  partial_function_graph (measure_set_density phi
    (@centered_closed_ball_relation R X) A) a 0 ->
  forall c : R, (0<c)%R -> exists d : R, (0<d)%R /\ forall r : R,
    (0<r)%R -> (r<d)%R -> phi (A `&` metric_closed_ball a r) <
      c%:E*phi (metric_closed_ball a r).
Proof.
move=> hm hballs hA c hc.
have [b [hb hsmall]] := @covering_finite_limit_small_values R _ _ _ a 0 c hA hc.
exists (b/3)%R; split; first by rewrite divr_gt0 // ltr0n.
move=> r hr hrd.
pose S := metric_closed_ball a r.
have hS : centered_closed_ball_relation a S by exists r.
have hdiam : extended_metric_diameter S<b%:E.
  have hd : extended_metric_diameter S <= (r+r)%R%:E.
    apply: (metric_diameter_least (extended_metric_diameter_specification S)).
    - rewrite lee_fin; exact: addr_ge0 (ltW hr) (ltW hr).
    - move=> x y hx hy; rewrite lee_fin; exact: metric_closed_ball_diameter_bound hx hy.
  apply: le_lt_trans hd _; rewrite lte_fin.
  have : (r*3<b)%R by move: hrd; rewrite ltr_pdivlMr ?ltr0n.
  lra.
have [hp hf] := hballs a r hr.
have hfa : phi (A `&` S) \is a fin_num.
  rewrite (ge0_fin_numE (measure_nonnegative hm _)).
  apply: le_lt_trans (@measure_mono R _ _ hm (A `&` S) S (fun x hx=>hx.2)) _.
  by move: hf; rewrite (ge0_fin_numE (ltW hp)).
have hq := @measure_ratio_positive_finite_denominator R _
  (measure_restrict phi A)
  phi S hp hf.
have hlt := (hsmall S _ hS hdiam hq).2; rewrite add0r in hlt.
exact: (@finite_measure_ratio_comparison R _ _ _ S c _ hfa hf hp hq hlt).
Qed.

(** Source for [centered_zero_density_isometric_preimage]: supporting
    change of coordinates in the scalar parameter used in Federer 3.1.4,
    p. 214. The hypotheses concern actual outer measures of all sets;
    no measurability of the density-zero set is required. *)
Theorem centered_zero_density_isometric_preimage (R : realType)
    (X Y : metricType R) (mu : set X -> \bar R) (nu : set Y -> \bar R)
    (f : X -> Y) (A : set Y) a :
  is_measure mu -> is_measure nu ->
  (forall x r, (0<r)%R -> 0<mu (metric_closed_ball x r) /\
    mu (metric_closed_ball x r) \is a fin_num) ->
  (forall y r, (0<r)%R -> 0<nu (metric_closed_ball y r) /\
    nu (metric_closed_ball y r) \is a fin_num) ->
  (forall x z, mdist (f x) (f z)=mdist x z) ->
  (forall B, nu B=mu (f @^-1` B)) ->
  partial_function_graph (measure_set_density nu
    (@centered_closed_ball_relation R Y) A) (f a) 0 ->
  partial_function_graph (measure_set_density mu
    (@centered_closed_ball_relation R X) (f @^-1` A)) a 0.
Proof.
move=> hm hn hbmu hbnu hiso hpush hA.
have hball r : f @^-1` metric_closed_ball (f a) r=metric_closed_ball a r.
  apply/seteqP; split=> x; change (mdist (f a) (f x)<=r -> mdist a x<=r)%R ||
    change (mdist a x<=r -> mdist (f a) (f x)<=r)%R; by rewrite hiso.
apply: (centered_small_mass_zero_density hm hbmu)=> c hc.
have [d [hd hs]] := centered_zero_density_small_mass hn hbnu hA hc.
exists d; split=> // r hr hrd.
have hh := hs r hr hrd.
by rewrite !hpush preimage_setI hball in hh.
Qed.

(** Source for [centered_approximate_limit_isometric_precompose]:
    approximate-limit form of the scalar coordinate identification in
    Federer 3.1.4, p. 214. Actual partial domains are transported by
    inverse image, exactly as for the exceptional neighborhood sets. *)
Theorem centered_approximate_limit_isometric_precompose (R : realType)
    (X Y : metricType R) (Z : topologicalType)
    (mu : set X -> \bar R) (nu : set Y -> \bar R) (f : X -> Y)
    (g : partial_function Y Z) a z :
  is_measure mu -> is_measure nu ->
  (forall x r, (0<r)%R -> 0<mu (metric_closed_ball x r) /\
    mu (metric_closed_ball x r) \is a fin_num) ->
  (forall y r, (0<r)%R -> 0<nu (metric_closed_ball y r) /\
    nu (metric_closed_ball y r) \is a fin_num) ->
  (forall x y, mdist (f x) (f y)=mdist x y) ->
  (forall B, nu B=mu (f @^-1` B)) ->
  is_measure_approximate_limit nu (@centered_closed_ball_relation R Y) g (f a) z ->
  is_measure_approximate_limit mu (@centered_closed_ball_relation R X)
    (partial_function_precompose f g) a z.
Proof.
move=> hm hn hbmu hbnu hiso hpush hg W hW.
rewrite partial_function_precompose_preimage preimage_setC.
exact: centered_zero_density_isometric_preimage hm hn hbmu hbnu hiso hpush (@hg W hW).
Qed.
