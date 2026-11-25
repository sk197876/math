(** A single-scale Bohr covering measure supporting Federer
    (1969), 2.8.20, p. 152. We retain the
    positive-core and harmonic estimates of Saks1934 Lemma B,
    pp. 258–259, and Cesari1939 Lemma III, pp. 306–307.
    Disjoint closed group unions are selected using the already
    proved 2.8.7, p. 144, in place of the sources'
    repeated finite packing. Their measures are summed by the
    abstract measure-sum laws. Source titles and departure:
    VitaliMassObstruction.v and QuadraticDiameterAdequacy.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  cardinality reals constructive_ereal topology ring lra.
From Federer Require Import RealMetricBackground MetricProductBackground ScalarPlaneRectangles ScalarMetricPlane SquareBohrUnions
  BohrGroupMeasure SmallRectangleMassCoverUP HarmonicPrefixBounds
  MeasureUP MeasureBasic MeasureAlmostBasic MeasureDisjointSupport MeasureSum
  NonnegativeSum NonnegativeSumScale BorelRegularMeasureUP TopologicalBorel
  MetricDiameter MetricClosedBalls CoveringFamilyUP CountablyClosedFamilyUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [selected_bohr_group_cover_exists]: supporting
    measure assembly for Federer 2.8.20, p. 152.
    Countably many disjoint closed fan unions inside the radius-two
    maximum-metric ball have total area at most sixteen.
    Summing their core measures therefore costs at most 32/H.
    Only the abstract group and measure-sum laws are used. *)
Theorem selected_bohr_group_cover_exists (R : realType) r (cap budget : R)
    (G : set (set (scalar_metric_plane R))) :
  (0<harmonic_partial_sum R r)%R -> (32/harmonic_partial_sum R r<=budget)%R ->
  (G `<=` @is_square_bohr_union R r cap) -> countable G -> set_family_disjoint G ->
  (\bigcup_(U in G) U) `<=` metric_closed_ball (((0:R)%R,(0:R)%R) : scalar_metric_plane R) 2 ->
  scalar_plane_lebesgue (@scalar_unit_square R `\` \bigcup_(U in G) U) = 0 ->
  exists nu C, is_small_rectangle_mass_cover cap budget nu C.
Proof.
move=> hH hbudget hGF hGc hGd hwithin hrem.
have hp2 : (0<=2 :> R)%R by rewrite ler0n.
have hex U : exists w : (set (scalar_metric_plane R) -> \bar R)*set (set (scalar_metric_plane R)),
    G U -> is_bohr_group_measure U cap 2 (2/harmonic_partial_sum R r)%R w.1 w.2.
  case: (pselect (G U))=> hU.
  - have [nu [C h]] := @square_bohr_group_measure_exists R r cap 2 U hH hp2 (hGF U hU).
    by exists (nu,C).
  - exists ((fun _ => 0),set0)=> h; exfalso; exact: hU h.
pose w U := projT1 (cid (hex U)).
have hw U : G U -> is_bohr_group_measure U cap 2 (2/harmonic_partial_sum R r)%R (w U).1 (w U).2 :=
  projT2 (cid (hex U)).
pose m U := (w U).1.
pose F U := (w U).2.
have hm U (hU : G U) : is_measure (m U) := bohr_group_measure_law (hw U hU).
have [nu hsum] := @measure_sum_exists R (scalar_metric_plane R)
  [the choiceType of set (scalar_metric_plane R)] G m.
pose C := \bigcup_(U in G) F U.
have hCrect S : C S -> is_nondegenerate_scalar_rectangle S.
  move=> [U hU hS]; exact (@bohr_group_measure_rectangles R U cap 2
    (2/harmonic_partial_sum R r)%R (m U) (F U) (hw U hU) S hS).
have hunion : (\bigcup_(S in C) S)=(\bigcup_(U in G) U).
  apply/seteqP; split.
  - move=> x [S [U hU hS] hx].
    exists U=> //; rewrite -(bohr_group_measure_union (hw U hU)); by exists S.
  - move=> x [U hU hx].
    have hxF : (\bigcup_(S in F U) S) x by rewrite (bohr_group_measure_union (hw U hU)).
    have [S hS hxS] := hxF; exists S=> //; by exists U.
have hcost : nu setT<=budget%:E.
  rewrite hsum.
  have hcoef : (0<=2/harmonic_partial_sum R r)%R := divr_ge0 hp2 (ltW hH).
  have hb : nonnegative_sum G (fun U => m U setT) <=
      nonnegative_sum G (fun U => (2/harmonic_partial_sum R r)%:E * scalar_plane_lebesgue U).
    apply: nonnegative_sum_mono=> U hU; exact: bohr_group_measure_cost (hw U hU).
  apply: le_trans hb _.
  rewrite (@nonnegative_sum_scale R [the choiceType of set (scalar_metric_plane R)] G
    (@scalar_plane_lebesgue R) (2/harmonic_partial_sum R r)%R hcoef
    (fun U _ => @measure_nonnegative R (scalar_metric_plane R) _ (scalar_plane_lebesgue_is_measure R) U)).
  have hGarea : nonnegative_sum G (@scalar_plane_lebesgue R)<=16.
    have hbarea : nonnegative_sum G (@scalar_plane_lebesgue R)<=
        scalar_plane_lebesgue (metric_closed_ball (((0:R)%R,(0:R)%R) : scalar_metric_plane R) 2).
      apply: (@measure_disjoint_sum_bound R (scalar_metric_plane R)
        [the choiceType of set (scalar_metric_plane R)] (@scalar_plane_lebesgue R)
        (scalar_plane_lebesgue_is_measure R) _ G idfun).
      + move=> U hU x hx; apply: hwithin; by exists U.
      + move=> U hU; apply: (@borel_regular_borel_measurable R (scalar_metric_plane R)
          (@scalar_plane_lebesgue R) (scalar_plane_lebesgue_is_measure R) (scalar_plane_borel_regular R)).
        apply: closed_borel_set.
        have [a [c [s [H [K [E [_ [hp ->]]]]]]]] := hGF U hU.
        exact: bohr_patch_closed_union_closed hp.
      + exact hGd.
    by move: hbarea; rewrite scalar_metric_plane_ball_area // -!natrM.
  have hcoefE : 0<=(2/harmonic_partial_sum R r)%:E by rewrite lee_fin.
  have hb16 := lee_wpmul2l hcoefE hGarea.
  apply: le_trans hb16 _; rewrite -EFinM lee_fin.
  have he : ((2/harmonic_partial_sum R r)*16=32/harmonic_partial_sum R r)%R by ring.
  by rewrite he.
exists nu,C; constructor.
- exact (@measure_sum_is_measure R (scalar_metric_plane R) _ G m nu hm hsum).
- move=> S hS; apply: (@measure_sum_measurable R (scalar_metric_plane R) _ G m nu S hm hsum).
  move=> U hU; exact (@bohr_group_measure_measurable R U cap 2
    (2/harmonic_partial_sum R r)%R (m U) (F U) (hw U hU) S hS).
- apply: bigcup_countable hGc _=> U hU.
  exact: finite_set_countable (bohr_group_measure_finite (hw U hU)).
- exact hCrect.
- move=> S [U hU hS]; exact (@bohr_group_measure_diameter R U cap 2
    (2/harmonic_partial_sum R r)%R (m U) (F U) (hw U hU) S hS).
- move=> S [U hU hS].
  apply: le_trans (@bohr_group_measure_mass R U cap 2
    (2/harmonic_partial_sum R r)%R (m U) (F U) (hw U hU) S hS) _.
  exact (@measure_sum_component_bound R (scalar_metric_plane R) _ G m nu U S hsum hU).
- by rewrite hunion.
- exact hcost.
Qed.

(** Source for [small_rectangle_mass_cover_exists]: supporting
    single-scale large-average construction for Federer 2.8.20,
    p. 152, in the measure form of Saks1934
    Lemma B, pp. 258–259. Both the diameter cap
    and the total-mass budget can be arbitrarily small.
    Harmonic unboundedness chooses the finite fan size;
    2.8.7 selects disjoint fan unions covering almost
    all of the unit square inside a fixed bounded open ball. *)
Theorem small_rectangle_mass_cover_exists (R : realType) (cap budget : R) :
  (0<cap)%R -> (0<budget)%R ->
  exists nu C, is_small_rectangle_mass_cover cap budget nu C.
Proof.
move=> hcap hbudget.
have [r [hr hH]] := @harmonic_partial_sums_unbounded R (32/budget)%R.
have hquot : (0<32/budget)%R by rewrite divr_gt0 // ltr0n.
have hHpos : (0<harmonic_partial_sum R r)%R := lt_trans hquot hH.
have hcost : (32/harmonic_partial_sum R r<=budget)%R.
  have hb : (32<budget*harmonic_partial_sum R r)%R by move: hH; rewrite ltr_pdivrMr // mulrC.
  apply: ltW; by rewrite ltr_pdivrMr.
have hadeq := @square_bohr_unions_adequate R r cap hr hHpos hcap.
pose V := metric_open_ball (((0:R)%R,(0:R)%R) : scalar_metric_plane R) 2.
have hVo : open V := metric_open_ball_open _ _.
have [G hG] := hadeq V hVo.
have hinside : @scalar_unit_square R `<=` V.
  move=> x hx; rewrite /V /metric_open_ball /= metric_product_distanceE
    !real_line_metric_distanceE /= !sub0r !normrN gt_max.
  move: hx; rewrite /scalar_unit_square /scalar_closed_rectangle /= !in_itv /=.
  move=> [/andP [hx1 hx2] /andP [hy1 hy2]].
  apply/andP; split; rewrite ger0_norm //; lra.
have hwithin : (\bigcup_(U in G) U) `<=` metric_closed_ball (((0:R)%R,(0:R)%R) : scalar_metric_plane R) 2.
  move=> x hx; have hh := @adequate_selection_within R (scalar_metric_plane R)
    (@scalar_plane_lebesgue R) (@is_square_bohr_union R r cap) setT V G hG x hx.
  exact: ltW hh.
have hrem : scalar_plane_lebesgue (@scalar_unit_square R `\` \bigcup_(U in G) U)=0.
  apply: (@measure_null_subset R (scalar_metric_plane R) (@scalar_plane_lebesgue R)
    (scalar_plane_lebesgue_is_measure R) _ (V `\` \bigcup_(U in G) U)).
  - move=> x [hx hn]; split=> //; exact: hinside x hx.
  - have hh := adequate_selection_remainder hG; by rewrite setIT in hh.
exact (@selected_bohr_group_cover_exists R r cap budget G hHpos hcost
  (adequate_selection_members hG) (adequate_selection_countable hG)
  (adequate_selection_disjoint hG) hwithin hrem).
Qed.
