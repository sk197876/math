(** Federer (1969), 2.9.15, pp. 160–161: the exceptional sets for
    centered-ball differentiation. The standing context of 2.9.1, p. 152,
    includes an existing phi Vitali relation. Supporting Federer 2.9.5.
    Erratum p. 3, book p. 161 line 11, corrects the later directional
    covering citation to 2.8.14. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  cardinality reals constructive_ereal topology lra.
From Federer Require Import MeasureUP MeasureBasic MeasureDerivationContext BorelRegularMeasureUP
  MetricClosedBalls CoveringFamilyUP CoveringFamilyLaws MetricDiameterUP DiametricRegularityUP
  DiameterWeightLaws WeightedEnlargements BallEnlargementBound WeightedCoverComparisonBound
  SmallBallRatioLoci UniformBallGrowthAdequacy BallCoverMeasureBounds TopologicalBorel.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ring_scope.
Local Open Scope ereal_scope.

(** Source for [growth_comparison_ball_family]: direct eligible
    ball family F in the first case of Federer 2.9.15,
    p. 161, with a fixed positive radius cap d. Each
    member retains a center in T, lies in E, and its
    fivefold ball has numerator mass less than b times the
    reference mass of the original ball. *)
Definition growth_comparison_ball_family (R : realType) (X : metricType R)
    (psi phi : set X -> \bar R) (T E : set X) (d b : R) : set (set X) :=
  [set S | S `<=` E /\ exists a r, T a /\ (0<r<d)%R /\
    S=metric_closed_ball a r /\ psi (metric_closed_ball a (5*r)%R)<b%:E*phi S].

(** Source for [growth_comparison_balls_cover]: supporting
    coverage assertion for F in the first case of Federer
    2.9.15, p. 161. Choose a small lower-comparison radius
    s and use r=s/5, so both the numerator comparison on
    the fivefold ball and the reference growth estimate apply.
    An open neighbourhood radius makes the original ball lie in E. *)
Lemma growth_comparison_balls_cover (R : realType) (X : metricType R)
    (psi phi : set X -> \bar R) (T E : set X) (d c lambda : R) :
  (0<d)%R -> (0<c)%R -> open E -> T `<=` E ->
  has_uniform_fivefold_ball_growth phi T d lambda ->
  (forall x, T x -> has_arbitrarily_small_lower_ball_ratio psi phi x c) ->
  T `<=` \bigcup_(S in growth_comparison_ball_family psi phi T E d (c*lambda)%R) S.
Proof.
move=> hd hc hE hTE hg hlow a ha.
have hnb : nbhs a E by rewrite openE in hE; exact: hE a (hTE a ha).
have [e he hEe] := (metricType_numDomainType.nbhs_mdistP a _).1 hnb.
have hcap : (0<Num.min d e)%R by rewrite lt_min hd he.
have [s [hs [hscap hmass]]] := hlow a ha (Num.min d e) hcap.
pose r := (s/5)%R.
have hr : (0<r)%R by rewrite /r divr_gt0 // ltr0n.
have hrs : (r<s)%R by rewrite /r; lra.
have hrd : (r<d)%R.
  apply: lt_trans hrs (lt_le_trans hscap _); by rewrite ge_min lexx.
have hre : (r<e)%R.
  apply: lt_trans hrs (lt_le_trans hscap _); by rewrite ge_min lexx orbT.
have h5 : (5*r=s)%R by rewrite /r mulrC divfK //; rewrite pnatr_eq0.
have hgr := hg a ha r hr hrd.
rewrite h5 in hgr.
have hscale := @lee_wpmul2l R c%:E (ltac:(by rewrite lee_fin; exact: ltW hc)) _ _ (ltW hgr).
rewrite muleA -EFinM in hscale.
have hbound := lt_le_trans hmass hscale.
exists (metric_closed_ball a r); last by rewrite /metric_closed_ball /= mdistxx; exact: ltW hr.
split.
- move=> x hx; apply: hEe; exact: le_lt_trans hx hre.
- exists a,r; split=> //; split; first by apply/andP; split.
  split=> //; by rewrite h5.
Qed.

(** Source for [uniform_growth_small_ratio_null]: direct first
    covering case of Federer 2.9.15, p. 161. The fixed
    lower-ratio coefficient c and fivefold growth lambda give
    psi(T)<=(c lambda) phi(E). Apply the disjoint weighted
    selection of 2.8.4–2.8.5 with diameter weight and tau=2;
    the enlargement of each chosen ball lies in its fivefold
    ball. Let the reference mass of the open superset tend
    to zero, as in the printed final paragraph. *)
Theorem uniform_growth_small_ratio_null (R : realType) (X : metricType R)
    (phi psi : set X -> \bar R) (T : set X) (d c lambda : R) :
  is_derivation_measure phi -> is_measure psi -> phi T=0 ->
  (0<d)%R -> (0<c)%R -> (1<lambda)%R ->
  has_uniform_fivefold_ball_growth phi T d lambda ->
  (forall x, T x -> has_arbitrarily_small_lower_ball_ratio psi phi x c) -> psi T=0.
Proof.
move=> hphi hpsi hz hd hc hl hg hlow; have hm := derivation_measure_law hphi.
have hb : (0<=c*lambda)%R := ltW (mulr_gt0 hc (lt_trans ltr01 hl)).
apply: (@null_measure_from_open_cover_bounds R X phi psi T (c*lambda)%R hphi hpsi hb hz).
move=> E hE hTE hEfin.
pose F := growth_comparison_ball_family psi phi T E d (c*lambda)%R.
have hcover := @growth_comparison_balls_cover R X psi phi T E d c lambda hd hc hE hTE hg hlow.
have hballs S : F S -> exists a r, T a /\ (0<r<d)%R /\
    S=metric_closed_ball a r /\ psi (metric_closed_ball a (5*r)%R)<(c*lambda)%R%:E*phi S.
  by move=> [_ h].
have hFE S : F S -> S `<=` E by move=> [h _].
have hbounded S : F S -> metric_set_bounded S.
  move=> hS; have [a [r [_ [/andP [hr _] [-> _]]]]] := hballs S hS.
  exact: covering_closed_ball_bounded (ltW hr).
have hnonempty S : F S -> S<>set0.
  move=> hS hzero; have [a [r [_ [/andP [hr _] [hSr _]]]]] := hballs S hS.
  have hx : S a by rewrite hSr /metric_closed_ball /= mdistxx; exact: ltW hr.
  by rewrite hzero in hx.
have hFm S : F S -> measure_measurable phi S.
  move=> hS; apply: (@borel_regular_borel_measurable R X phi hm (derivation_measure_borel_regular hphi)).
  have [a [r [_ [_ [-> _]]]]] := hballs S hS.
  apply: closed_borel_set; exact: metric_closed_ball_closed.
have hpos S : F S -> 0<phi S.
  move=> hS; rewrite lt_def (measure_nonnegative hm) andbT.
  apply/negP=> /eqP hzero; have [a [r [_ [_ [_ hcmp]]]]] := hballs S hS.
  rewrite hzero mule0 in hcmp.
  by have := le_lt_trans (measure_nonnegative hpsi _) hcmp; rewrite ltxx.
have [w hw] := @real_diameter_weight_exists R X F hbounded.
have hwn := @diameter_weight_nonnegative R X F w hw.
have hwb : exists b, forall S, F S -> (w S<=b)%R.
  exists (d+d)%R=> S hS; have [a [r [_ [/andP [hr hrd] [hSr _]]]]] := hballs S hS.
  have hB : F (metric_closed_ball a r) by rewrite -hSr.
  rewrite hSr; apply: le_trans (@diameter_weight_ball_bound R X F w hw a r hB (ltW hr)) _.
  exact: lerD (ltW hrd) (ltW hrd).
have hhat S : F S -> psi (weighted_enlargement F w 2%R S)<=(c*lambda)%R%:E*phi S.
  move=> hS; have [a [r [_ [/andP [hr _] [hSr hcmp]]]]] := hballs S hS.
  have hB : F (metric_closed_ball a r) by rewrite -hSr.
  have hinc := @diameter_enlargement_ball_bound R X F w 2%R hw
    (ltac:(by rewrite ler0n)) a r hB (ltW hr).
  have he : ((1+2*2)*r=5*r)%R by lra.
  rewrite he in hinc; rewrite -hSr in hinc.
  exact: le_trans (@measure_mono R X psi hpsi _ _ hinc) (ltW hcmp).
exact: (@weighted_cover_comparison_bound R X phi psi T E F w 2%R (c*lambda)%R
  hm hpsi (ltac:(by rewrite ltr1n)) hb hEfin hnonempty hwn hwb hFE hFm hpos hcover hhat).
Qed.
