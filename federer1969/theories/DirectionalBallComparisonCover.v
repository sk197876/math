(** Federer (1969), 2.9.15, pp. 160–161: the exceptional sets for
    centered-ball differentiation. The standing context of 2.9.1, p. 152,
    includes an existing phi Vitali relation. Supporting Federer 2.9.5.
    Erratum p. 3, book p. 161 line 11, corrects the later directional
    covering citation to 2.8.14. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  cardinality reals constructive_ereal topology lra.
From Federer Require Import MeasureUP MeasureBasic MeasureDerivationContext BorelRegularMeasureUP
  MetricClosedBalls CoveringFamilyUP MetricSubsetBackground MetricSubsetSeparability
  DirectionalLimitationUP CenteredBallFamilyCaps CenteredBallCoverUP CenteredBallCover
  DisjointDenseBallFamilies SmallBallRatioLoci FiniteColouredCoverComparison
  BallCoverMeasureBounds TopologicalBorel.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ring_scope.
Local Open Scope ereal_scope.

(** Source for [lower_comparison_ball_family]: direct family F'
    in the second case of Federer 2.9.15, p. 161.
    Balls have centers in T, positive radii below mu, lie
    in E, and satisfy the strict lower mass comparison. *)
Definition lower_comparison_ball_family (R : realType) (X : metricType R)
    (psi phi : set X -> \bar R) (T E : set X) (mu c : R) : set (set X) :=
  [set S | S `<=` E /\ exists a r, T a /\ (0<r<mu)%R /\
    S=metric_closed_ball a r /\ psi S<c%:E*phi S].

(** Source for [lower_comparison_balls_at_target]: supporting
    small-ball coverage needed in the second case of Federer
    2.9.15, p. 161. The arbitrary small lower-ratio
    condition localises simultaneously to the radius cap and
    to the open neighbourhood E containing the target. *)
Lemma lower_comparison_balls_at_target (R : realType) (X : metricType R)
    (psi phi : set X -> \bar R) (T E : set X) (mu c : R) :
  (0<mu)%R -> open E -> T `<=` E ->
  (forall x, T x -> has_arbitrarily_small_lower_ball_ratio psi phi x c) ->
  has_small_centered_balls mu (lower_comparison_ball_family psi phi T E mu c) T.
Proof.
move=> hmu hE hTE hlow a ha.
have hnb : nbhs a E by rewrite openE in hE; exact: hE a (hTE a ha).
have [e he hEe] := (metricType_numDomainType.nbhs_mdistP a _).1 hnb.
have hcap : (0<Num.min mu e)%R by rewrite lt_min hmu he.
have [r [hr [hrcap hb]]] := hlow a ha (Num.min mu e) hcap.
have hrmu : (r<mu)%R.
  apply: lt_le_trans hrcap _; by rewrite ge_min lexx.
have hre : (r<e)%R.
  apply: lt_le_trans hrcap _; by rewrite ge_min lexx orbT.
exists r; split; first by apply/andP; split.
split.
- move=> x hx; apply: hEe; exact: le_lt_trans hx hre.
- exists a,r; split=> //; split; first by apply/andP; split.
  by split.
Qed.

(** Source for [directional_small_ratio_null]: direct second
    covering case of Federer 2.9.15, p. 161. Apply
    2.8.14 as corrected by erratum p. 3, book p. 161
    line 11, to obtain 2 zeta+1 disjoint colour families.
    Their countability follows from separability. Summing the
    mass comparisons bounds psi(T) by (2 zeta+1)c phi(E),
    and open approximation of the reference-null target gives
    zero. The numerator measure needs only its measure laws
    for this supporting implication. *)
Theorem directional_small_ratio_null (R : realType) (X : metricType R)
    (phi psi : set X -> \bar R) (T : set X) (xi : \bar R) (eta c : R) (zeta : nat) :
  is_derivation_measure phi -> is_measure psi -> phi T=0 ->
  (exists D : set X, countable D /\ dense D) ->
  is_directionally_limited_at T xi eta zeta -> (0<c)%R ->
  (forall x, T x -> has_arbitrarily_small_lower_ball_ratio psi phi x c) -> psi T=0.
Proof.
move=> hphi hpsi hz hsep hdir hc hlow; have hm := derivation_measure_law hphi.
pose N := (2*zeta+1)%N.
have hcoef : (0<=N%:R*c :> R)%R by apply: mulr_ge0; [exact: ler0n|exact: ltW hc].
apply: (@null_measure_from_open_cover_bounds R X phi psi T (N%:R*c)%R hphi hpsi hcoef hz).
move=> E hE hTE hEfin.
have [mu [hmu hsmall]] := @positive_directional_radius_cap R xi (directional_radius_positive hdir).
pose F := lower_comparison_ball_family psi phi T E mu c.
have hballs S : F S -> exists a r, T a /\ (0<r<mu)%R /\
    S=metric_closed_ball a r /\ psi S<c%:E*phi S.
  by move=> [_ h].
have hFsmall : is_small_closed_ball_family mu F.
  move=> S hS; have [a [r [_ [hr [hSr _]]]]] := hballs S hS.
  by exists a,r.
have hcent := @lower_comparison_balls_at_target R X psi phi T E mu c hmu hE hTE hlow.
have [G hG] := @federer_2_8_14 R X T xi eta mu zeta F hdir hmu hsmall hFsmall hcent.
have hsepT := @metric_subset_separable R X T hsep.
have hcount i : countable (G i).
  apply: (@separable_centered_disjoint_balls_countable R X T (G i) hsepT _
    (@finite_ball_cover_disjoint X F T N G hG i)).
  move=> S hS; have hSF := @finite_ball_cover_members X F T N G hG i S hS.
  have [a [r [ha [/andP [hr _] [hSr _]]]]] := hballs S hSF.
  by exists a,r; split=> //; split.
have hwithin i S : G i S -> S `<=` E.
  move=> hS; exact: (@finite_ball_cover_members X F T N G hG i S hS).1.
have hmeas i S : G i S -> measure_measurable phi S.
  move=> hS; apply: (@borel_regular_borel_measurable R X phi hm (derivation_measure_borel_regular hphi)).
  have hSF := @finite_ball_cover_members X F T N G hG i S hS.
  have [a [r [_ [_ [-> _]]]]] := hballs S hSF.
  apply: closed_borel_set; exact: metric_closed_ball_closed.
have hcell i S : G i S -> psi S<=c%:E*phi S.
  move=> hS; have hSF := @finite_ball_cover_members X F T N G hG i S hS.
  have [a [r [_ [_ [_ hcmp]]]]] := hballs S hSF.
  exact: ltW hcmp.
have hbound := @finite_coloured_cover_comparison_bound R X [the finType of 'I_N]
  phi psi T E G c hm hpsi (ltW hc) hEfin hcount
  (@finite_ball_cover_disjoint X F T N G hG) hwithin hmeas hcell
  (@finite_ball_cover_covers X F T N G hG).
by rewrite card_ord in hbound.
Qed.
