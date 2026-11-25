(** Federer (1969), 2.9.15, pp. 160–161: the exceptional sets for
    centered-ball differentiation. The standing context of 2.9.1, p. 152,
    includes an existing phi Vitali relation. Supporting Federer 2.9.5.
    Erratum p. 3, book p. 161 line 11, corrects the later directional
    covering citation to 2.8.14. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  cardinality reals constructive_ereal topology lra.
From Federer Require Import MeasureUP MeasureBasic MeasureAlmostBasic MeasureDerivationContext
  NullBallLocus CenteredRatioInfinity FivefoldBallGrowth UniformBallGrowthAdequacy
  SmallBallRatioLoci GrowthBallComparisonCover DirectionalBallComparisonCover
  CenteredDensityGeometry DirectionalLimitationUP DirectionalLimitationLaws MetricClosedBalls
  ExtendedRealReciprocalBounds.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ring_scope.
Local Open Scope ereal_scope.

(** Source for [growth_null_set_outside_infinite_density]: direct
    first-alternative null-set implication in Federer 2.9.15,
    pp. 160–161. Countable positive natural lower-ratio
    coefficients, natural growth coefficients, and reciprocal
    radius cutoffs cover the target. Each uniform piece is
    numerator-null by the printed fivefold-ball covering estimate.
    The pieces need not be measurable or disjoint. *)
Theorem growth_null_set_outside_infinite_density (R : realType) (X : metricType R)
    (phi psi : set X -> \bar R) (T : set X) :
  is_derivation_measure phi -> is_measure psi ->
  (forall x, fivefold_ball_ratio_upper_limit phi x< +oo) ->
  T `<=` ~` (measure_infinite_centered_density_points psi phi `|` measure_null_ball_points phi) ->
  phi T=0 -> psi T=0.
Proof.
move=> hphi hpsi hgrowth hTout hz; have hm := derivation_measure_law hphi.
pose A (p : (nat*(nat*nat))%type) := T `&` [set x |
  has_arbitrarily_small_lower_ball_ratio psi phi x (p.1.+1%:R : R) /\
  forall r : R, (0<r)%R -> (r<((p.2.2.+1%:R : R)^-1))%R ->
    phi (metric_closed_ball x (5*r)%R)<((p.2.1+2)%:R : R)%:E*phi (metric_closed_ball x r)].
have hAnull p : psi (A p)=0.
  have hphiA : phi (A p)=0.
    apply: (@measure_null_subset R X phi hm _ T _ hz); by move=> x [hx _].
  have hd : (0<(p.2.2.+1%:R : R)^-1)%R by rewrite invr_gt0 ltr0n.
  have hc : (0<p.1.+1%:R :> R)%R by rewrite ltr0n.
  have hl : (1<(p.2.1+2)%:R :> R)%R by rewrite ltr1n addn2 !ltnS leq0n.
  apply: (@uniform_growth_small_ratio_null R X phi psi (A p)
    ((p.2.2.+1%:R : R)^-1)%R (p.1.+1%:R : R) ((p.2.1+2)%:R : R)
    hphi hpsi hphiA hd hc hl).
  - by move=> x [_ [_ hb]] r; exact: hb r.
  - by move=> x [_ [h _]].
have hcover : T `<=` \bigcup_p A p.
  move=> x hx.
  have hout : ~ (measure_infinite_centered_density_points psi phi x \/ measure_null_ball_points phi x) := hTout x hx.
  have hnP : ~ measure_null_ball_points phi x by move=> hp; exact: hout (or_intror hp).
  have hnW : ~ measure_infinite_centered_density_points psi phi x by move=> hw; exact: hout (or_introl hw).
  have [i hi] := @outside_infinite_density_small_comparison R X psi phi x hphi hnP hnW.
  have [lambda [d [hl [hd hb]]]] := @finite_fivefold_ball_growth_cutoff R X phi x hphi hnP (hgrowth x).
  pose n := Num.bound lambda.
  have hln : (0<=lambda)%R := ltW (lt_trans ltr01 hl).
  have hnat : (lambda<(n+2)%:R)%R.
    apply: lt_le_trans (archi_boundP hln) _; by rewrite ler_nat leq_addr.
  have [m hmcut] := @positive_reciprocal_nat_small R d hd.
  exists (i,(n,m))=> //; split=> //; split=> // r hr hrd.
  have hsmall : (r<d)%R := lt_trans hrd hmcut.
  apply: lt_le_trans (hb r hr hsmall) _.
  have hco : lambda%:E<=((n+2)%:R : R)%:E by rewrite lee_fin; exact: ltW hnat.
  exact: (@lee_wpmul2r R (phi (metric_closed_ball x r))
    (@measure_nonnegative R X phi hm (metric_closed_ball x r)) _ _ hco).
apply: (@measure_null_subset R X psi hpsi _ (\bigcup_p A p) hcover).
exact (@measure_null_countable_union R X _ psi hpsi setT A
  (@countableP (nat*(nat*nat))%type setT) (fun p _ => hAnull p)).
Qed.

(** Source for [directional_null_set_outside_infinite_density]:
    direct second-alternative null-set implication in Federer
    2.9.15, pp. 160–161. Intersect the target with the
    countable directional cover and the positive natural lower-
    ratio loci. Directional limitation is inherited by subsets;
    each resulting target is numerator-null by 2.8.14's finite
    disjoint covering bound. The numerator needs only its measure
    laws for this supporting null-set implication. *)
Theorem directional_null_set_outside_infinite_density (R : realType) (X : metricType R)
    (phi psi : set X -> \bar R) (T : set X) (K : set (set X)) :
  is_derivation_measure phi -> is_measure psi ->
  (exists D : set X, countable D /\ dense D) -> countable K ->
  (\bigcup_(B in K) B)=setT ->
  (forall B, K B -> exists (xi : \bar R) (eta : R) (zeta : nat),
    is_directionally_limited_at B xi eta zeta) ->
  T `<=` ~` (measure_infinite_centered_density_points psi phi `|` measure_null_ball_points phi) ->
  phi T=0 -> psi T=0.
Proof.
move=> hphi hpsi hsep hK hKcover hdir hTout hz; have hm := derivation_measure_law hphi.
pose D := (@setT nat) `*` K.
pose A (p : (nat*set X)%type) := T `&` (p.2 `&`
  [set x | has_arbitrarily_small_lower_ball_ratio psi phi x (p.1.+1%:R : R)]).
have hD : countable D := countableX (countableP setT) hK.
have hAnull p : D p -> psi (A p)=0.
  move=> [_ hpK]; have [xi [eta [zeta hlim]]] := hdir p.2 hpK.
  have hphiA : phi (A p)=0.
    apply: (@measure_null_subset R X phi hm _ T _ hz); by move=> x [hx _].
  have hdirA : is_directionally_limited_at (A p) xi eta zeta.
    apply: (@directional_limit_subset R X (A p) p.2 xi eta zeta) hlim.
    by move=> x [_ [hx _]].
  apply: (@directional_small_ratio_null R X phi psi (A p) xi eta (p.1.+1%:R : R) zeta
    hphi hpsi hphiA hsep hdirA (ltac:(by rewrite ltr0n))).
  by move=> x [_ [_ hx]].
have hcover : T `<=` \bigcup_(p in D) A p.
  move=> x hx.
  have hout : ~ (measure_infinite_centered_density_points psi phi x \/ measure_null_ball_points phi x) := hTout x hx.
  have hnP : ~ measure_null_ball_points phi x by move=> hp; exact: hout (or_intror hp).
  have hnW : ~ measure_infinite_centered_density_points psi phi x by move=> hw; exact: hout (or_introl hw).
  have [n hn] := @outside_infinite_density_small_comparison R X psi phi x hphi hnP hnW.
  have hxK : (\bigcup_(B in K) B) x by rewrite hKcover.
  have [B hBK hxB] := hxK.
  exists (n,B); first by split.
  by split=> //; split.
apply: (@measure_null_subset R X psi hpsi _ (\bigcup_(p in D) A p) hcover).
exact: (@measure_null_countable_union R X [the choiceType of (nat*set X)%type]
  psi hpsi D A hD hAnull).
Qed.

(** Source for [geometric_null_set_outside_infinite_density]:
    complete null-set implication needed for the opposite
    inequality in Federer 2.9.15, pp. 160–161. Both
    original geometric alternatives are retained; arbitrary
    reference-null subsets outside W union P are numerator-null. *)
Theorem geometric_null_set_outside_infinite_density (R : realType) (X : metricType R)
    (phi psi : set X -> \bar R) (T : set X) :
  is_derivation_measure phi -> is_measure psi -> is_centered_density_geometry phi ->
  T `<=` ~` (measure_infinite_centered_density_points psi phi `|` measure_null_ball_points phi) ->
  phi T=0 -> psi T=0.
Proof.
move=> hphi hpsi; case=> hg hT hz.
- exact: growth_null_set_outside_infinite_density hphi hpsi hg hT hz.
- have [hsep [K [hK [hcover hdir]]]] := hg.
  exact: directional_null_set_outside_infinite_density hphi hpsi hsep hK hcover hdir hT hz.
Qed.
