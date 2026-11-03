(** Regression examples for Federer's covering theorems.
    Sources and editions: CoveringFamilyUP.v. These examples
    test strict ball inequalities, fine coverings and measure
    adequacy, empty and overlapping targets, and the empty-set
    obstruction and zero-weight boundary for weighted selections,
    and empty/singleton center-radius selections. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets cardinality reals constructive_ereal topology.
From Federer Require Import NonnegativeSum MeasureUP MeasureBasic
  MetricClosedBalls CoveringTheorems EuclideanLebesgueDimensions PointMassMeasure
  RealNormUP NormMetric NormMetricContinuity LinearBasis FiniteCoordinates MetricSubsetBackground MetricDiameter MetricDiameterMaps MetricDiameterUP PartialFunctionUP PartialFunctionBasic
  BorelPartition TopologicalBorel ExtendedRealBounds.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [covering_zero_radius_distinguishes_balls]:
    boundary regression for B(a,r) and U(a,r) in Federer
    2.8.1, p. 141. The set formulas extend to r=0:
    the center is in the closed ball and not in the open ball. *)
Example covering_zero_radius_distinguishes_balls (R : realType)
    (X : metricType R) (a : X) :
  metric_closed_ball a 0%R a /\ ~ metric_open_ball a 0%R a.
Proof.
by rewrite /metric_closed_ball /metric_open_ball /= mdistxx lexx ltxx.
Qed.

(** Source for [empty_enlargement_family_covers_empty_union]: empty-family
    boundary of Federer 2.8.5, p. 144 The corollary does not require an
    eligible member when F itself is empty. *)
Example empty_enlargement_family_covers_empty_union (R : realType)
    (X : choiceType) (d : set X -> R) (tau : R) :
  (\bigcup_(T in (@set0 (set X))) T) `<=`
    \bigcup_(S in (@set0 (set X))) weighted_enlargement set0 d tau S.
Proof.
have hG : is_weighted_cover_selection set0 d tau (@set0 (set X)).
  constructor; [by move=> T []|by move=> T S []|by move=> T []].
exact: weighted_selection_enlargement_cover hG.
Qed.

(** Source for [singleton_recurrent_enumeration_repeats]: boundary
    regression for the repeated enumeration in Federer 2.8.2, p. 142 A
    singleton family is permitted, so the family need not be infinite. *)
Example singleton_recurrent_enumeration_repeats (J : choiceType) (j : J)
    (hn : exists k, [set j] k) N :
  exists n, (N <= n)%N /\
    @recurrent_enumeration J [set j] (countable1 j) hn n = j.
Proof.
exact (@recurrent_enumeration_cofinal J [set j]
  (@recurrent_enumeration J [set j] (countable1 j) hn)
  (@recurrent_enumeration_specification J [set j] (countable1 j) hn) j (erefl _) N).
Qed.

(** Source for [null_remainder_needs_no_finite_selection]: null-error
    boundary of the finite selection in Federer 2.8.2, pp. 142–143 The empty
    subfamily works for every factor, including zero, when the tested target
    has zero measure. This auxiliary fact does not relax the theorem's
    strict factor bounds. *)
Example null_remainder_needs_no_finite_selection (R : realType)
    (X : metricType R) (mu : set X -> \bar R)
    (F : set (set X)) (A W : set X) :
  mu (W `&` A) = 0 ->
  finite_set (@set0 (set X)) /\
    is_contraction_cover_selection mu F A W 0%R set0.
Proof.
move=> hz; split; first exact: finite_set0.
exact: empty_contraction_cover_selection hz.
Qed.

(** Source for [contraction_criterion_empty_targets]: empty-K
    boundary of Federer 2.8.2, p. 142. A recurrent eligible
    enumeration is unavailable for an empty family; the public
    theorem still gives adequacy for its empty union. *)
Example contraction_criterion_empty_targets (R : realType)
    (X : metricType R) (F : set (set X)) (mu : set X -> \bar R) :
  is_covering_theory_context F mu ->
  family_is_measure_adequate mu F set0.
Proof.
move=> hc.
pose s (A : {A : set X | (@set0 (set X)) A}) : R := False_rect R (svalP A).
have hs A : (0 < s A < 1)%R by case: A=> A [].
have hl A : has_local_cover_contraction mu F (sval A) (s A).
  by case: A=> A [].
have h := @federer_2_8_2 R X F set0 mu s hc (@countable0 (set X)) hs hl.
by rewrite bigcup_set0 in h.
Qed.

(** Source for [singleton_family_is_fine]: regression for the
    fine-cover definition in Federer 2.8.1, p. 142. All
    singletons form a fine covering of any metric space; no
    positivity of the singleton's diameter is required. *)
Example singleton_family_is_fine (R : realType) (X : metricType R) :
  family_covers_finely [set B : set X | exists x, B = [set x]] setT.
Proof.
move=> a _ e he; exists [set a]; split; first by exists a.
split; first by [].
by move=> x ->; rewrite /metric_open_ball /= mdistxx.
Qed.

(** Source for [null_measure_adequacy_need_not_be_fine]:
    regression distinguishing the two definitions of Federer
    2.8.1, p. 142. For the zero measure the empty family is
    adequate for a singleton, but it is not a fine covering.
    This is a local example, not a claimed counterexample to
    a statement in Federer. *)
Example null_measure_adequacy_need_not_be_fine (R : realType)
    (X : metricType R) (a : X) :
  family_is_measure_adequate (fun _ : set X => (0 : \bar R)) set0 [set a] /\
  ~ family_covers_finely set0 [set a].
Proof.
have hm : @is_measure R X (fun _ => 0).
  constructor; first by move=> B.
  move=> B F hF hcov; rewrite (nonnegative_sum_zero (fun C hC => erefl _)).
  exact: lexx.
split; first exact: (@adequate_family_null_target R X (fun _ => 0) hm set0 [set a] (erefl _)).
move=> hf; have he := (fine_cover_empty_family [set a]).1 hf.
have ha : [set a] a by [].
by rewrite he in ha.
Qed.

(** Source for [adequate_targets_union_without_disjointness]: finite-family
    regression for Federer 2.8.3, p. 143 The two targets may overlap or
    coincide: disjointness is a condition on selections, not on the targets
    whose adequacy is combined. *)
Example adequate_targets_union_without_disjointness (R : realType)
    (X : metricType R) (F : set (set X)) (mu : set X -> \bar R)
    (A B : set X) :
  is_covering_theory_context F mu ->
  family_is_measure_adequate mu F A -> family_is_measure_adequate mu F B ->
  family_is_measure_adequate mu F (A `|` B).
Proof.
move=> hc hA hB.
pose K := [set A] `|` [set B].
have hK : countable K := finite_set_countable (finite_set2 A B).
have hmember C : K C -> family_is_measure_adequate mu F C.
  by move=> [->|->].
have he : (\bigcup_(C in K) C) = A `|` B.
  apply/seteqP; split.
  - by move=> x [C [->|->] hx]; [left|right].
  - move=> x [hx|hx].
    * exists A=> //; by left.
    * exists B=> //; by right.
have h := @adequate_family_countable_union R X F K mu hc hK hmember.
by rewrite he in h.
Qed.

(** Source for [empty_member_obstructs_weighted_selection]: Supporting
    Federer 2.8.4, p. 143.No eligible set can have a nonempty intersection
    with the empty target, for any weights or factor. *)
Example empty_member_obstructs_weighted_selection (R : realType)
    (X : choiceType) (d : set X -> R) (tau : R) :
  ~ exists G, is_weighted_cover_selection [set (@set0 X)] d tau G.
Proof.
move=> [G hG].
have [S [hS [hne _]]] := @weighted_selection_dominates R X [set (@set0 X)] d tau G
  hG set0 (erefl _).
apply: hne; exact: set0I.
Qed.

(** Source for [zero_weight_singleton_selection]: regression for the
    nonnegative, rather than positive, weight in Federer 2.8.4, p. 143 A
    singleton family of a nonempty set selects itself even when its weight
    is zero. *)
Example zero_weight_singleton_selection (R : realType)
    (X : choiceType) (A : set X) (tau : R) :
  A <> set0 ->
  is_weighted_cover_selection [set A] (fun _ => (0%R : R)) tau [set A].
Proof.
move=> hA; constructor.
- by move=> T.
- move=> T S -> -> hne; exfalso; by apply: hne.
- move=> T ->; exists A; split; first reflexivity.
  split; first by rewrite setIid.
  by rewrite mulr0.
Qed.

(** Source for [finite_weighted_selection_covers_fine_target]: finite-G
    regression for Federer 2.8.6, p. 144 Taking H=G makes the family of
    remaining enlargements empty, so a finite selected family covers every
    point of the fine target. *)
Example finite_weighted_selection_covers_fine_target (R : realType)
    (X : metricType R) (F : set (set X)) (d : set X -> R)
    (tau : R) (G : set (set X)) (A : set X) :
  (forall S, F S -> closed S) -> family_covers_finely F A ->
  is_weighted_cover_selection F d tau G -> finite_set G ->
  A `<=` \bigcup_(S in G) S.
Proof.
move=> hc hf hG hfin x hx.
case: (pselect ((\bigcup_(S in G) S) x))=> [hu|hn]; first exact hu.
have hsub : G `<=` G by [].
have hr : (A `\` \bigcup_(S in G) S) x by split.
have [S [hS hnS] _] := @weighted_selection_finite_remainder_cover R X F d tau G A
  hc hf hG G hfin hsub x hr.
exfalso; exact: hnS hS.
Qed.

(** Source for [zero_measure_excludes_strict_enlargement_control]:
    strict-inequality boundary in Federer 2.8.7, p. 144 A zero-measure
    member cannot satisfy the strict enlargement estimate. This is the
    positivity step used to obtain countability of the selected family. *)
Example zero_measure_excludes_strict_enlargement_control (R : realType)
    (X : choiceType) (mu : set X -> \bar R) (hm : is_measure mu)
    (F : set (set X)) (d : set X -> R) (tau lambda : R) (S : set X) :
  mu S = 0 -> ~ mu (weighted_enlargement F d tau S) < lambda%:E * mu S.
Proof.
move=> hz hbound.
have hp := @strict_enlargement_bound_positive R X mu hm F d tau lambda S hbound.
by rewrite hz ltxx in hp.
Qed.

(** Source for [empty_family_enlargement_criterion]: empty-F and
    empty-target regression for Federer 2.8.7, p. 144 The strict estimate is
    vacuous on an empty family, which is allowed. *)
Example empty_family_enlargement_criterion (R : realType) (X : metricType R)
    (mu : set X -> \bar R) :
  is_covering_theory_context set0 mu -> family_is_measure_adequate mu set0 set0.
Proof.
move=> hc.
pose d (S : {S : set X | (@set0 (set X)) S}) : R := False_rect R (svalP S).
have hn S : (0 <= d S)%R by case: S=> S [].
have hb : exists C : R, forall S, (d S <= C)%R.
  exists 0%R; by move=> [S []].
have h2 : (1 < (2 : R))%R by rewrite ltr1n.
have he S : mu (family_weighted_enlargement d 2%R S) < 2%R%:E * mu (sval S).
  by case: S=> S [].
exact (@federer_2_8_7 R X set0 mu set0 d 2%R 2%R hc
  (@fine_cover_empty_target R X set0) hn hb h2 h2 he).
Qed.

(** Source for [empty_radius_family_selection]: empty-Q
    boundary of Federer 2.8.10, p. 147. The lemma
    requires neither an eligible pair nor an inhabited ambient
    metric space; the radius bound is positive and finite. *)
Example empty_radius_family_selection (R : realType) (X : metricType R) :
  exists P, is_radius_cover_selection (2%R : R) (@set0 (X * R)) P.
Proof.
have ht : (1 < (2 : R))%R by rewrite ltr1n.
have hm : (0 < (1 : R))%R := ltr01.
have hQ : is_bounded_positive_radius_family (1%R : R) (@set0 (X * R)).
  by move=> p [].
exact (@federer_2_8_10 R X 2%R 1%R set0 ht hm hQ).
Qed.

(** Source for [singleton_radius_family_selects_itself]:
    singleton regression for both conditions in Federer
    2.8.10, p. 147. The selected pair may dominate
    itself, and positive r with tau>1 gives the required
    STRICT bound r/tau<r. *)
Example singleton_radius_family_selects_itself (R : realType) (X : metricType R)
    (a : X) (r tau : R) : (0 < r)%R -> (1 < tau)%R ->
  is_radius_cover_selection tau [set (a,r)] [set (a,r)].
Proof.
move=> hr ht.
have ht0 : (0 < tau)%R := lt_trans ltr01 ht.
constructor.
- by move=> p.
- move=> p q -> -> hne; exfalso; by apply: hne.
- move=> q ->; exists (a,r); split; first reflexivity.
  split.
  * by rewrite /= mdistxx addr_ge0 ?ltW.
  * by rewrite /= ltr_pdivrMr // ltr_pMr.
Qed.

(** Source for [zero_dimensional_closed_ball_volume]: zero-dimensional
    regression for the Euclidean growth example of Federer 2.8.8,
    p. 145. The project's L^0 convention is unit mass at the
    sole vector, extending 2.6.5, pp. 119–120. *)
Example zero_dimensional_closed_ball_volume (R : realType) :
  @euclidean_closed_unit_volume R 0 = 1%R.
Proof.
rewrite /euclidean_closed_unit_volume /euclidean_lebesgue_measure point_mass_in //=.
by rewrite /metric_closed_ball /= mdistxx ler01.
Qed.

(** Source for [empty_ball_family_diametric_regularity]: empty-family
    boundary of the strict diametric-regularity condition in
    Federer 2.8.8, p. 145. The estimate is vacuous even
    when the ambient measure vanishes. *)
Example empty_ball_family_diametric_regularity (R : realType)
    (X : metricType R) (mu : set X -> \bar R) (tau lambda : R) :
  is_diametrically_regular_ball_family mu (@set0 (set X)) tau lambda.
Proof. by move=> a r hr []. Qed.

(** Source for [empty_target_directional_limitation]: empty-target
    boundary in Federer 2.8.9, p. 145. The cardinal
    condition is vacuous; the original parameter bounds remain. *)
Example empty_target_directional_limitation (R : realType) (X : metricType R)
    (xi : \bar R) (eta : R) (zeta : nat) :
  0 < xi -> (0 < eta <= 1/3)%R -> (0 < zeta)%N ->
  is_directionally_limited_at (@set0 X) xi eta zeta.
Proof.
move=> hx he hz; constructor=> // a [].
Qed.

(** Source for [singleton_target_directional_limitation]: a singleton
    requires at most one direction, supporting the cardinal convention
    of Federer 2.8.9, p. 145. The punctured target is in
    fact empty, without assuming existence of radial points. *)
Example singleton_target_directional_limitation (R : realType) (X : metricType R)
    (a : X) (xi : \bar R) (eta : R) :
  0 < xi -> (0 < eta <= 1/3)%R ->
  is_directionally_limited_at [set a] xi eta 1.
Proof.
move=> hx he.
apply: (@directional_limit_from_finite_cardinal_bound R X [set a] xi eta 1 hx he (ltnSn 0)).
have hc := @card_set1 X a.
rewrite (card_le_eql hc) -(card_le_eqr (@card_II 1)); exact: card_lexx.
Qed.

(** Source for [directional_factor_at_endpoint]: the endpoint
    eta=1/3 in Federer 2.8.11, p. 147. The same
    explicit tau=33/32 still satisfies both STRICT parameter
    inequalities, including the strict upper bound by one. *)
Example directional_factor_at_endpoint (R : realType) :
  has_directional_cover_factor (1/3 : R) (ratr (33/32 : rat)).
Proof.
apply: directional_cover_factor_uniform.
by rewrite lexx andbT divr_gt0 ?ltr01 ?ltr0n.
Qed.

(** Source for [two_empty_parts_leave_one_parameter]: the
    extra one in card P<=2 zeta+1, Federer 2.8.11,
    p. 147. For the supporting set-theoretic lemma zeta=0
    is permitted: both parts can be empty while the
    distinguished parameter remains. *)
Example two_empty_parts_leave_one_parameter (T : choiceType) (p : T) :
  ([set p] #<= [set: 'I_(2*0+1)])%card.
Proof.
apply: (@two_part_cardinal_bound T [set p] set0 set0 p 0).
- by move=> x hx; left.
- exact: card_ge0.
- exact: card_ge0.
Qed.

(** Source for [infinite_directional_radius_allows_finite_ball_bound]:
    xi=infinity is allowed by Federer 2.8.9, p. 146,
    and retained in the radius hypothesis of 2.8.12, p. 148.
    Every finite real bound is less than infinity/2. *)
Example infinite_directional_radius_allows_finite_ball_bound (R : realType) (mu : R) :
  mu%:E < (1/2 : R)%:E * +oo.
Proof. by rewrite extended_half_radius_boundE ltry. Qed.

(** Source for [empty_parameter_family_decomposition]: empty-Q
    boundary of the decomposition in Federer 2.8.12, p. 149.
    Every color class may be empty, including zero classes in
    the supporting decomposition specification. *)
Example empty_parameter_family_decomposition (R : realType) (X : metricType R) (N : nat) :
  is_radius_parameter_decomposition (@set0 (X*R)) (fun _ : 'I_N => set0).
Proof.
constructor.
- by move=> i p [].
- by move=> i p q [].
- apply/seteqP; split=> [p []|p [i _ []]].
Qed.

(** Source for [empty_controlled_ball_decomposition]: empty-Q
    regression for the full corollary of Federer 2.8.12,
    pp. 148–149. No ambient point is required. The original
    positive zeta, strict factor and positive finite radius bound
    are supplied even though the eligible family is empty. *)
Example empty_controlled_ball_decomposition (R : realType) (X : metricType R) :
  exists G : 'I_3 -> set (set X),
    is_disjoint_ball_family_decomposition (associated_closed_ball_family (@set0 (X*R))) G.
Proof.
pose tau : R := ratr (33/32 : rat).
have hf : has_directional_cover_factor (1/3 : R) tau := directional_factor_at_endpoint R.
have ht : (1 < tau)%R := hf.1.
have he : (0 < (1/3 : R) <= 1/3)%R by rewrite lexx andbT divr_gt0 ?ltr01 ?ltr0n.
have hlim : is_directionally_limited_at (@set0 X) +oo%E (1/3 : R) 1.
  constructor.
  - exact: lt0y.
  - exact he.
  - exact: ltnSn.
  - by move=> a [].
have hQ : is_controlled_ball_family tau (@set0 (X*R)).
  constructor.
  - exact ht.
  - by move=> p [].
  - by move=> p q [].
have hA (p : X*R) : (@set0 (X*R)) p -> (@set0 X) p.1 by [].
have hb : is_bounded_positive_radius_family (1 : R) (@set0 (X*R)) by move=> p [].
have hm : (0 < (1 : R))%R := ltr01.
have hs : ((1 : R)%:E < (1/2 : R)%:E * +oo)%E :=
  infinite_directional_radius_allows_finite_ball_bound (1 : R).
exact (@federer_2_8_12 R X set0 +oo%E (1/3 : R) tau 1%R 1 set0 hlim hf hm hQ hA hb hs).
Qed.

(** Source for [empty_controlled_center_selection]: empty eligible
    family regression for Federer 2.8.13, pp. 149–150.
    The full theorem supplies a selected subset, whose membership
    law forces it to be empty, without an ambient point. *)
Example empty_controlled_center_selection (R : realType) (X : metricType R) :
  is_controlled_center_selection (2 : R) (@set0 (X*R)) set0.
Proof.
have ht : (1 < (2 : R))%R by rewrite ltr1n.
have hm : (0 < (1 : R))%R := ltr01.
have hQ : is_bounded_positive_radius_family (1 : R) (@set0 (X*R)) by move=> p [].
have [P hs] := @federer_2_8_13 R X 2%R 1%R set0 ht hm hQ.
have he : P = set0.
  apply/seteqP; split=> [p hp|p []].
  exact (@controlled_center_selection_members R X 2%R set0 P hs p hp).
by rewrite he in hs.
Qed.

(** Source for [singleton_center_cover_must_select_parameter]:
    singleton regression for the center-coverage conclusion of
    Federer 2.8.13, p. 149. Covering the eligible center
    forces a selected member, and membership forces that member
    to be the original parameter. *)
Example singleton_center_cover_must_select_parameter (R : realType) (X : metricType R)
    (tau : R) (p : X*R) (P : set (X*R)) :
  is_controlled_center_selection tau [set p] P -> P = [set p].
Proof.
move=> hs.
have [q [hq _]] := @controlled_center_selection_covers R X tau [set p] P hs p (erefl _).
have hqp : q=p := @controlled_center_selection_members R X tau [set p] P hs q hq.
apply/seteqP; split.
- move=> w hw; exact (@controlled_center_selection_members R X tau [set p] P hs w hw).
- by move=> w ->; rewrite -hqp.
Qed.

(** Source for [empty_centered_ball_cover]: empty-target and
    empty-family boundary of the complete theorem in Federer
    2.8.14, p. 150. The strict positive radius bound and
    directional parameters are supplied without an ambient point. *)
Example empty_centered_ball_cover (R : realType) (X : metricType R) :
  exists G : 'I_3 -> set (set X),
    is_finite_disjoint_ball_cover (@set0 (set X)) (@set0 X) G.
Proof.
have he : (0 < (1/3 : R) <= 1/3)%R by rewrite lexx andbT divr_gt0 ?ltr01 ?ltr0n.
have hlim : is_directionally_limited_at (@set0 X) +oo%E (1/3 : R) 1.
  constructor.
  - exact: lt0y.
  - exact he.
  - exact: ltnSn.
  - by move=> a [].
have hm : (0 < (1 : R))%R := ltr01.
have hsmall : ((1 : R)%:E < (1/2 : R)%:E * +oo)%E :=
  infinite_directional_radius_allows_finite_ball_bound (1 : R).
have hF : is_small_closed_ball_family (1 : R) (@set0 (set X)) by move=> B [].
have hc : has_small_centered_balls (1 : R) (@set0 (set X)) set0 by move=> a [].
exact (@federer_2_8_14 R X set0 +oo%E (1/3 : R) 1%R 1 set0 hlim hm hsmall hF hc).
Qed.

(** Source for [empty_ball_family_covers_only_empty_target]:
    the point-coverage conclusion of Federer 2.8.14, p. 150,
    cannot hold for a nonempty target if F is empty. This
    regression checks the union of selected balls in the abstract
    conclusion, independently of the existence construction. *)
Example empty_ball_family_covers_only_empty_target (X : choiceType)
    (A : set X) (N : nat) (G : 'I_N -> set (set X)) :
  is_finite_disjoint_ball_cover (@set0 (set X)) A G -> A = set0.
Proof.
move=> h; apply/seteqP; split=> [a ha|a []].
have [i _ [B hB _]] := @finite_ball_cover_covers X set0 A N G h a ha.
exact (@finite_ball_cover_members X set0 A N G h i B hB).
Qed.

(** Source for [empty_radius_family_not_centered_fine]: the
    zero radius-infimum premise of Federer 2.8.15, p. 150,
    fails when there are no eligible radii at a target point.
    This checks the empty-infimum convention through the proved
    equivalence with arbitrarily small positive radii. *)
Example empty_radius_family_not_centered_fine (R : realType) (X : metricType R) (a : X) :
  ~ has_zero_centered_radius_infimum (@set0 (set X)) [set a].
Proof.
move=> hi.
have hs := (centered_radius_infimum_zero_iff_small_balls (@set0 (set X)) [set a]).1 hi.
have [r [_ hF]] := hs a (erefl _) 1%R (@ltr01 R); exact hF.
Qed.

(** Source for [one_measurable_cover_zero_remainder]: one-color
    boundary of the supporting finite-cover estimate in Federer
    2.8.15, p. 150. For N=1 its loss factor is zero.
    The book uses N=2 zeta+1 with positive zeta; this regression
    checks the stronger supporting estimate at its smallest index. *)
Example one_measurable_cover_zero_remainder (R : realType) (X : choiceType)
    (phi : set X -> \bar R) (hm : is_measure phi) (T U : set X) :
  phi T < +oo -> measure_measurable phi U -> T `<=` U -> phi (T `\` U) = 0.
Proof.
move=> hT hU hTU.
have hc : T `<=` \bigcup_(i in @setT 'I_1) U by move=> x hx; exists ord0=> //; exact: hTU x hx.
have [i hi] := @finite_measurable_cover_contraction R X phi hm T 1 (fun _ => U)
  (ltnSn 0) hT (fun _ => hU) hc.
have hz : finite_cover_loss_factor R 1 = 0%R by rewrite /finite_cover_loss_factor invr1 subrr.
apply/eqP; rewrite eq_le (measure_nonnegative hm _) andbT.
by move: hi; rewrite hz mul0e.
Qed.

(** Source for [empty_centered_fine_family_adequacy]: empty-target
    regression for the complete corollary of Federer 2.8.15,
    p. 150. The target subspace is empty and separable, and
    the radius-infimum premise is vacuous. No ambient point
    is chosen; the standing measure context is retained. *)
Example empty_centered_fine_family_adequacy (R : realType) (X : metricType R)
    (phi : set X -> \bar R) :
  is_covering_theory_context (@set0 (set X)) phi -> family_is_measure_adequate phi set0 set0.
Proof.
move=> hc.
have he : (0 < (1/3 : R) <= 1/3)%R by rewrite lexx andbT divr_gt0 ?ltr01 ?ltr0n.
have hlim : is_directionally_limited_at (@set0 X) +oo%E (1/3 : R) 1.
  constructor.
  - exact: lt0y.
  - exact he.
  - exact: ltnSn.
  - by move=> a [].
have hm : (0 < (1 : R))%R := ltr01.
have hsmall : ((1 : R)%:E < (1/2 : R)%:E * +oo)%E :=
  infinite_directional_radius_allows_finite_ball_bound (1 : R).
have hF : is_small_closed_ball_family (1 : R) (@set0 (set X)) by move=> B [].
have hsep : exists D : set (metric_subset (@set0 X)), countable D /\ dense D.
  exists set0; split; first exact: countable0.
  move=> U [a _] _; exfalso; exact: (set_valP a).
have hz : has_zero_centered_radius_infimum (@set0 (set X)) (@set0 X) by move=> a [].
exact (@federer_2_8_15 R X phi set0 set0 +oo%E (1/3 : R) 1%R 1 hc hlim hm hsmall hF hsep hz).
Qed.


(** Source for [empty_covering_relation_not_fine]: empty-fiber
    regression for the zero-infimum definition in Federer
    2.8.16, p. 151. A target point must have arbitrarily
    small related sets, rather than an empty choice of sets. *)
Example empty_covering_relation_not_fine (R : realType) (X : metricType R) (x : X) :
  ~ covering_relation_fine_at (fun (_ : X) (_ : set X) => False) x.
Proof.
move=> hf; have [S [hS _]] := (covering_relation_fine_iff_small_diameter _ x).1 hf 1%R (@ltr01 R).
exact hS.
Qed.

(** Source for [singleton_covering_relation_fine]: degenerate
    diameter-zero regression for Federer 2.8.16, p. 151.
    Singletons are allowed in a covering relation; the definition
    does not require positive diameters. *)
Example singleton_covering_relation_fine (R : realType) (X : metricType R) :
  is_covering_relation (fun (x : X) S => S = [set x]) /\
  forall x, covering_relation_fine_at (fun (x : X) S => S = [set x]) x.
Proof.
split; first by move=> x S ->.
move=> x; apply: (covering_relation_fine_iff_small_diameter _ x).2=> e he.
exists [set x]; split=> //; by rewrite extended_metric_diameter_singleton lte_fin.
Qed.

(** Source for [empty_function_has_no_covering_limit]: the domain
    qualification of Federer 2.8.16, p. 151 Fineness of the ambient relation
    cannot supply missing function values. *)
Example empty_function_has_no_covering_limit (R : realType) (X : metricType R)
    (C : X -> set X -> Prop) (x : X) :
  ~ partial_function_domain (covering_relation_limit C (@partial_function_empty (set X) (\bar R))) x.
Proof.
move=> /covering_limit_domain [_ h].
by rewrite covering_upper_limit_empty_function covering_lower_limit_empty_function in h.
Qed.


(** Source for [zero_denominator_cannot_control_enlargement]:
    regression for the necessary positivity correction in the
    erratum, p. 3, book p. 151 line 24, to Federer
    2.8.17. A totalized reciprocal at zero cannot recover
    the enlargement bound from a numerical ratio cutoff. The
    theorem excludes this denominator, rather than treating this
    calculation as defined division in Federer's convention. *)
Example zero_denominator_cannot_control_enlargement (R : realType) :
  (0 : R)%:E + (1 : R)%:E * ((0 : R)^-1)%:E < (2 : R)%:E /\
  ~ ((1 : R)%:E < (2 : R)%:E * (0 : R)%:E).
Proof.
split.
- by rewrite invr0 mule0 add0e lte_fin ltr0n.
- by rewrite mule0 lte_fin ltr10.
Qed.

(** Source for [cutoff_equality_is_not_fine]: the strict
    inequality in the cutoff relation C_n of Federer 2.8.17,
    p. 151. A function constantly equal to the cutoff
    contributes no eligible sets, even if the original relation
    is fine at the point. *)
Example cutoff_equality_is_not_fine (R : realType) (X : metricType R)
    (C : X -> set X -> Prop) (x : X) :
  ~ covering_relation_fine_at
    (covering_value_cutoff C (partial_function_total (fun _ : set X => (1 : R)%:E)) (1 : R)%:E) x.
Proof.
move=> hf.
have [S [[_ [y [hy hb]]] _]] := (covering_relation_fine_iff_small_diameter _ x).1 hf 1%R (@ltr01 R).
by move: hb; rewrite -hy ltxx.
Qed.

(** Source for [infinite_enlargement_fails_finite_cutoff]: the
    ratio cutoff in Federer 2.8.17, pp. 151–152, rules
    out infinite enlargement measure locally, without adding
    global finiteness of all enlargements as a hypothesis. *)
Example infinite_enlargement_fails_finite_cutoff (R : realType) (d q n : R) :
  (0 < q)%R -> ~ (d%:E + +oo * (q^-1)%:E < n%:E)%E.
Proof.
move=> hq; have hi : (0 < (q^-1)%:E)%E by rewrite lte_fin invr_gt0.
by rewrite (gt0_mulye hi) addey.
Qed.


(** Source for [singleton_ball_radius_reduction]: the radius
    conversion needed in Federer 2.8.18, p. 152. A
    singleton ball can have a large given radius, yet the
    same set has every smaller positive radius at that center.
    This checks the isolated-point case without diameter=2r. *)
Example singleton_ball_radius_reduction (R : realType) (X : metricType R)
    (x : X) (r t : R) :
  (0 < t < r)%R -> metric_closed_ball x r = [set x] ->
  metric_closed_ball x r = metric_closed_ball x t.
Proof.
move=> /andP [ht htr] he.
have hr : (0 < r)%R := lt_trans ht htr.
have hd : (extended_metric_diameter (metric_closed_ball x r) < t%:E)%E.
  by rewrite he extended_metric_diameter_singleton lte_fin.
have h := @closed_ball_small_radius_representation R X x r t hr ht hd.
by rewrite (min_r (ltW htr)) in h.
Qed.

(** Source for [centered_vitali_empty_ambient_space]: empty
    ambient-space regression for the complete theorem in Federer
    2.8.18, p. 152. An empty directional cover suffices;
    the proof cannot require an arbitrary ambient point. *)
Example centered_vitali_empty_ambient_space (R : realType) (X : metricType R)
    (phi : set X -> \bar R) :
  (forall x : X, False) ->
  is_covering_theory_context
    (covering_relation_image (@centered_closed_ball_relation R X) setT) phi ->
  is_vitali_relation phi (@centered_closed_ball_relation R X).
Proof.
move=> hempty hc.
have hs : exists D : set X, countable D /\ dense D.
  exists set0; split; first exact: countable0.
  by move=> U [x _]; exfalso; exact: hempty x.
have hcover : (\bigcup_(A in (@set0 (set X))) A) = setT.
  apply/seteqP; split=> [x _|x _]; first exact I.
  exfalso; exact: hempty x.
apply: (@federer_2_8_18 R X phi set0 hc hs (countable0 _) hcover).
by move=> A [].
Qed.


(** Source for [partition_empty_cell_is_maximal]: empty-cell
    regression for maximal members in Federer 2.8.19,
    p. 152. A Borel partition can contain the empty set;
    maximality does not arbitrarily exclude it when it is the
    sole eligible member. Its union still covers no points. *)
Example partition_empty_cell_is_maximal (X : Type) :
  is_maximal_family_member [set (@set0 X)] set0.
Proof. split=> // T ->; exact: subset_refl. Qed.

(** Source for [stable_one_cell_partition_vitali]: zero-diameter
    and stable-level regression for Federer 2.8.19, p. 152.
    If the metric ambient space has at most one point,
    the same one-cell partition can be repeated at every level.
    The measure need not assign positive mass to that cell. *)
Example stable_one_cell_partition_vitali (R : realType) (X : metricType R)
    (phi : set X -> \bar R) :
  is_measure phi -> (forall x y : X, x = y) ->
  is_vitali_relation phi (partition_covering_relation (fun _ : nat => [set (@setT X)])).
Proof.
move=> hm hpoint.
pose P := fun _ : nat => [set (@setT X)].
have hp : is_refining_borel_partitions P.
  constructor.
  - move=> n; exact: borel_partition_singleton (open_borel_set openT).
  - move=> n S ->; exists [set (@setT X)]; split; first exact: subset_refl.
    exact: bigcup_set1.
have hd : extended_metric_diameter (@setT X) = 0.
  apply/eqP; rewrite eq_le (metric_diameter_nonnegative (extended_metric_diameter_specification _)) andbT.
  apply: (metric_diameter_least (extended_metric_diameter_specification _))=> // x y _ _.
  by rewrite (hpoint x y) mdistxx.
apply: (@refining_partitions_vitali R X phi P hm hp)=> e he.
have heE : (0 < e%:E)%E by rewrite lte_fin.
exists 0%N; apply: le_lt_trans _ heE.
  apply: extended_real_sup_least=> d [S hS <-].
  by rewrite hS hd.
Qed.

(** Source for [harmonic_prefix_empty_boundary]: zero-length
    harmonic-sum regression for the finite fan construction
    supporting Federer 2.8.20, p. 152; Cesari1939
    Lemma III, p. 306. Positive fan sizes are
    required separately, so the empty prefix has its usual value. *)
Example harmonic_prefix_empty_boundary (R : realType) :
  harmonic_partial_sum R 0 = 0%R.
Proof. by rewrite harmonic_partial_sumE big_ord0. Qed.

(** Source for [one_member_bohr_fan_unit_area]: smallest
    positive fan-size regression for the construction supporting
    Federer 2.8.20, p. 152; Saks1934 (4), p. 258.
    A one-member fan has area one; it cannot provide
    an arbitrarily small member/union ratio. *)
Example one_member_bohr_fan_unit_area (R : realType)
    (F : 'I_1 -> set (R*R)) (E : set (R*R)) :
  is_bohr_fan F E -> scalar_plane_lebesgue (F ord0) = 1.
Proof. by move=> hF; rewrite (bohr_fan_equal_area hF ord0) invr1. Qed.

(** Source for [rectangle_removing_itself_empty_partition]:
    empty-remainder regression for the finite packing infrastructure
    supporting Federer 2.8.20, p. 152. Removing
    a set from itself requires no nonempty output cell. *)
Example rectangle_removing_itself_empty_partition (R : realType) (Q : set (R*R)) :
  is_finite_half_open_partition (Q `\` Q) set0.
Proof. by rewrite setDv; exact: empty_half_open_partition. Qed.

(** Source for [zero_area_rectangle_not_eligible]: nondegeneracy
    regression for the eligible family in Federer 2.8.20,
    p. 152. A null coordinate rectangle cannot
    be an eligible product of two nondegenerate compact intervals. *)
Example zero_area_rectangle_not_eligible (R : realType) (S : set (R*R)) :
  scalar_plane_lebesgue S = 0 -> ~ is_nondegenerate_scalar_rectangle S.
Proof.
move=> he hS; have hp := nondegenerate_scalar_rectangle_positive hS.
by rewrite he ltxx in hp.
Qed.

(** Source for [unit_rectangle_boundary_nonempty_null]: boundary
    regression for the half-open auxiliary companions in the
    construction supporting Federer 2.8.20, p. 152.
    Their deleted boundary is null but contains the upper
    corner. Equal area is not equality of sets. *)
Example unit_rectangle_boundary_nonempty_null (R : realType) :
  let K := scalar_closed_rectangle (0:R)%R 1 0 1 in
  let H := scalar_half_open_rectangle (0:R)%R 1 0 1 in
  scalar_plane_lebesgue (K `\` H) = 0 /\ (K `\` H) ((1:R)%R,(1:R)%R).
Proof.
move=> K H; split.
- exact (@closed_rectangle_half_open_remainder_null R 0 1 0 1 ler01 ler01).
- split.
  + by rewrite /K /scalar_closed_rectangle /= !in_itv /= ler01 lexx.
  + rewrite /H /scalar_half_open_rectangle /= !in_itv /= ltxx andbF.
    move=> [hbad _]; discriminate hbad.
Qed.

(* Federer 2.8.8, p. 145: supplementary growth-to-adequacy laws. *)
From Federer Require Import BallPowerGrowthAdequacy.

From Federer Require Import StrictConvexNorm StrictConvexRadial.

(** Source for [strict_convex_zero_radius_regression]: Federer 2.8.9,
    p. 146, radial uniqueness; regression at actual radius zero, proving
    that no division by a nonzero radius is implicit in the new theorem. *)
Example strict_convex_zero_radius_regression (R:realType) (V:lmodType R)
    (N:V->R) (hN:is_real_norm N) (hs:is_strictly_convex_norm N)
    (a b x:real_norm_metric_space hN):
  is_radial_projection_configuration a b a x -> x=a.
Proof.
move=>hx.
have ha:is_radial_projection_configuration a b a a.
  split; first by rewrite mdistxx; exact:mdist_ge0.
  split; first by [].
  by rewrite mdistxx subr0.
exact:(@strict_convex_radial_projection_unique R V N hN hs a b a x a hx ha).
Qed.
