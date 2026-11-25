(** Closed finite fan unions supporting Federer (1969),
    2.8.20, p. 152. The finite groups of Saks1934
    Lemma B, pp. 258–259, and Cesari1939 Lemma III,
    pp. 306–307, are placed in small squares. Their
    union area controls squared diameter. Federer 2.8.7,
    p. 144, can therefore select disjoint groups instead
    of repeating the finite remainder packing. This local proof
    route is a documented departure, not a statement correction.
    Source comparisons: QuadraticDiameterAdequacy.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  cardinality reals constructive_ereal topology ring lra.
From Federer Require Import ScalarPlaneRectangles ScalarHalfOpenRectangles ScalarMetricPlane
  RectangleCompanionContainment BohrPatchUP BohrPatchSealed BohrPatchLaws
  HarmonicPrefixBounds MeasureUP MeasureBasic MetricDiameterUP MetricDiameter
  CoveringFamilyUP DiametricRegularityUP DiameterWeightLaws QuadraticDiameterAdequacy.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory numFieldTopology.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [is_square_bohr_union]: supporting family of
    closed finite fan unions for Federer 2.8.20, p. 152.
    The cap bounds the parent side, not its area; eligible
    individual rectangles remain nondegenerate and closed. *)
Definition is_square_bohr_union (R : realType) r (cap : R)
    (U : set (scalar_metric_plane R)) :=
  exists (a c s : R) (H K : 'I_r -> set (R*R)) E,
    (0<s<=cap)%R /\
    is_bohr_patch (scalar_half_open_rectangle a (a+s)%R c (c+s)%R) H K E /\
    U=\bigcup_(i in @setT 'I_r) K i.

(** Source for [bohr_patch_closed_union_subset]: supporting
    bound on closed fan unions in the proof of Federer
    2.8.20, p. 152. It follows from companion
    containment, without unfolding the placed fan witness. *)
Lemma bohr_patch_closed_union_subset (R : realType) (a b c d : R) r
    (H K : 'I_r -> set (R*R)) (E : set (R*R)) :
  is_bohr_patch (scalar_half_open_rectangle a b c d) H K E ->
  (\bigcup_(i in @setT 'I_r) K i) `<=` scalar_closed_rectangle a b c d.
Proof.
move=> hp x [i _ hx].
exact (@rectangle_companion_parent_inclusion R (H i) (K i) a b c d
  (bohr_patch_companions hp i) (@bohr_patch_inclusion R (scalar_half_open_rectangle a b c d) r H K E hp i) x hx).
Qed.

(** Source for [bohr_patch_closed_union_closed]: closedness
    of each finite group union used in the application of
    Federer 2.8.7 to 2.8.20, p. 152. *)
Lemma bohr_patch_closed_union_closed (R : realType) (Q : set (R*R)) r
    (H K : 'I_r -> set (R*R)) (E : set (R*R)) :
  is_bohr_patch Q H K E ->
  closed (\bigcup_(i in @setT 'I_r) K i : set (scalar_metric_plane R)).
Proof.
move=> hp; apply: (@closed_bigcup _ [the choiceType of 'I_r] setT K (@finite_finset _ setT)).
move=> i _; have [a [b [c [d [_ [_ [_ ->]]]]]]] := bohr_patch_companions hp i.
exact: scalar_plane_rectangle_closed.
Qed.

(** Source for [bohr_patch_closed_union_gain]: supporting
    harmonic area gain for the closed group union in Federer
    2.8.20, p. 152; Cesari1939 Lemma III, p. 306.
    Passing from auxiliary half-open cells to their closed
    companions can only increase the union measure. *)
Lemma bohr_patch_closed_union_gain (R : realType) (Q : set (R*R)) r
    (H K : 'I_r -> set (R*R)) (E : set (R*R)) :
  is_bohr_patch Q H K E ->
  (harmonic_partial_sum R r/r%:R)%:E * scalar_plane_lebesgue Q <=
    scalar_plane_lebesgue (\bigcup_(i in @setT 'I_r) K i).
Proof.
move=> hp; apply: le_trans (bohr_patch_area_gain hp) _.
apply: (@measure_mono R [the choiceType of (R*R)%type] _ (scalar_plane_lebesgue_is_measure R)).
move=> x [i _ hx]; exists i=> //.
exact (@rectangle_companions_inclusion R (H i) (K i) (bohr_patch_companions hp i) x hx).
Qed.

(** Source for [square_bohr_union_diameter]: supporting
    diameter bound for the small closed groups used for
    Federer 2.8.20, p. 152. The maximum metric
    gives the parent side as an upper bound. *)
Lemma square_bohr_union_diameter (R : realType) r (cap : R)
    (U : set (scalar_metric_plane R)) :
  is_square_bohr_union r cap U -> extended_metric_diameter U <= cap%:E.
Proof.
move=> [a [c [s [H [K [E [/andP [hs hcap] [hp ->]]]]]]]].
apply: le_trans (scalar_square_subset_diameter (ltW hs) (bohr_patch_closed_union_subset hp)) _.
by rewrite lee_fin.
Qed.

(** Source for [square_bohr_union_quadratic_area]: supporting
    area control of squared diameter in the fan-union selection
    for Federer 2.8.20, p. 152. The coefficient
    H_r/r is positive under the stated harmonic hypothesis. *)
Lemma square_bohr_union_quadratic_area (R : realType) r (cap : R)
    (U : set (scalar_metric_plane R)) (d : R) :
  (0<harmonic_partial_sum R r)%R -> is_square_bohr_union r cap U ->
  is_extended_metric_diameter U d%:E ->
  0<scalar_plane_lebesgue U /\ ((harmonic_partial_sum R r/r%:R)*d*d)%:E <= scalar_plane_lebesgue U.
Proof.
move=> hH [a [c [s [H [K [E [/andP [hs hcap] [hp hU]]]]]]]] hd.
have hr : (0<r%:R :> R)%R by rewrite ltr0n; exact: bohr_patch_size hp.
have hcoef : (0<harmonic_partial_sum R r/r%:R)%R by rewrite divr_gt0.
have hd0 : (0<=d)%R by move: (metric_diameter_nonnegative hd); rewrite lee_fin.
have hds : (d<=s)%R.
  have hb := scalar_square_subset_diameter (ltW hs) (bohr_patch_closed_union_subset hp).
  have he := @metric_diameter_unique R (scalar_metric_plane R) U
    (extended_metric_diameter U) d%:E (extended_metric_diameter_specification U) hd.
  by move: hb; rewrite -hU he lee_fin.
have hgain := bohr_patch_closed_union_gain hp.
have haw : (a<=a+s)%R by lra.
have hcw : (c<=c+s)%R by lra.
rewrite -hU (scalar_half_open_rectangle_value haw hcw) in hgain.
have hearea : ((a+s-a)*(c+s-c)=s*s)%R by ring.
rewrite hearea -EFinM in hgain; split.
- apply: lt_le_trans _ hgain; by rewrite lte_fin mulr_gt0 // mulr_gt0.
- apply: le_trans _ hgain; rewrite lee_fin.
  have hsq : (d*d<=s*s)%R := le_trans (ler_wpM2r hd0 hds) (ler_wpM2l (ltW hs) hds).
  have hb := ler_wpM2l (ltW hcoef) hsq.
  by move: hb; rewrite mulrA.
Qed.

(** Source for [square_bohr_unions_fine]: arbitrarily small
    finite groups based at each point in the supporting
    construction for Federer 2.8.20, p. 152.
    The cap remains fixed and positive; the sealed placement's
    lower-corner law puts the base point in every eligible cell. *)
Lemma square_bohr_unions_fine (R : realType) r (cap : R) :
  (0<r)%N -> (0<cap)%R ->
  family_covers_finely (@is_square_bohr_union R r cap) setT.
Proof.
move=> hr hcap x _ e he.
pose s := (Num.min cap (e/2))%R.
have hehalf : (0<e/2)%R by rewrite divr_gt0 // ltr0n.
have hs : (0<s)%R by rewrite /s lt_min hcap hehalf.
have hscap : (s<=cap)%R by rewrite /s ge_min lexx.
have hsehalf : (s<=e/2)%R by rewrite /s ge_min lexx orbT.
have hhalf : (e/2<e)%R.
  by rewrite ltr_pdivrMr ?ltr0n // -{1}(mulr1 e) ltr_pM2l // ltr1n.
have hse : (s<e)%R := le_lt_trans hsehalf hhalf.
pose Q := scalar_half_open_rectangle x.1 (x.1+s)%R x.2 (x.2+s)%R.
have hQ : is_nondegenerate_half_open_rectangle Q.
  exists x.1,(x.1+s)%R,x.2,(x.2+s)%R; split; first by rewrite ltrDl.
  split=> //; by rewrite ltrDl.
pose p := @BohrPatch.value R r Q hr hQ.
have hp : is_bohr_patch Q p.1.1 p.1.2 p.2 := @BohrPatch.laws R r Q hr hQ.
pose U := \bigcup_(i in @setT 'I_r) p.1.2 i.
have hxlow : is_rectangle_lower_corner Q x.
  split.
  - by rewrite /Q /scalar_half_open_rectangle /= !in_itv /= !lexx !ltrDl hs.
  - move=> y; rewrite /Q /scalar_half_open_rectangle /= !in_itv /=.
    by move=> [/andP [hx _] /andP [hy _]]; split.
have hxU : U x.
  exists (Ordinal hr)=> //; exact (@bohr_patch_anchor R Q r p.1.1 p.1.2 p.2 hp x hxlow (Ordinal hr)).
exists U; split.
- exists x.1,x.2,s,p.1.1,p.1.2,p.2; split; first by rewrite hs hscap.
  by split.
- split=> // y hy.
  have hsub := @bohr_patch_closed_union_subset R x.1 (x.1+s)%R x.2 (x.2+s)%R
    r p.1.1 p.1.2 p.2 hp.
  have hd := @scalar_square_pair_distance R x.1 x.2 s x y (hsub x hxU) (hsub y hy).
  exact: le_lt_trans hd hse.
Qed.

(** Source for [square_bohr_unions_adequate]: supporting
    disjoint-group selection in the proof of Federer 2.8.20,
    p. 152. This applies the already formalised 2.8.7,
    p. 144, to closed fan unions. It replaces only
    the repeated finite packing argument of Saks1934 Lemma B,
    pp. 258–259; the positive-core and harmonic estimates
    remain those of the expanded source construction. *)
Theorem square_bohr_unions_adequate (R : realType) r (cap : R) :
  (0<r)%N -> (0<harmonic_partial_sum R r)%R -> (0<cap)%R ->
  @family_is_measure_adequate R (scalar_metric_plane R) (@scalar_plane_lebesgue R)
    (@is_square_bohr_union R r cap) setT.
Proof.
move=> hr hH hcap.
pose F := @is_square_bohr_union R r cap.
have hclosed S : F S -> closed S.
  move=> [a [c [s [H [K [E [_ [hp ->]]]]]]]]; exact: bohr_patch_closed_union_closed hp.
have hc := @scalar_plane_covering_context R F hclosed.
have hbounded S : F S -> metric_set_bounded S.
  move=> hS; apply: le_lt_trans (square_bohr_union_diameter hS) _; exact: ltry.
have [d hd] := @real_diameter_weight_exists R (scalar_metric_plane R) F hbounded.
have hdnon S (hS : F S) : (0<=d S)%R := @diameter_weight_nonnegative R _ F d hd S hS.
have hdb : exists B, forall S, F S -> (d S<=B)%R.
  exists cap=> S hS.
  have he := @metric_diameter_unique R (scalar_metric_plane R) S
    (extended_metric_diameter S) (d S)%:E (extended_metric_diameter_specification S) (hd S hS).
  by have := square_bohr_union_diameter hS; rewrite he lee_fin.
have hM : (0<=4 :> R)%R by rewrite ler0n.
have hcoef : (0<harmonic_partial_sum R r/r%:R)%R by rewrite divr_gt0 // ltr0n.
apply: (@quadratic_diameter_family_adequate R (scalar_metric_plane R) F
  (@scalar_plane_lebesgue R) d setT 4 (harmonic_partial_sum R r/r%:R)%R
  hc hd hdb (square_bohr_unions_fine hr hcap) hM hcoef).
- move=> a t ht; exact: le_eqVlt (scalar_metric_plane_ball_area a ht) ||
    by rewrite scalar_metric_plane_ball_area.
- move=> S hS; exact (@square_bohr_union_quadratic_area R r cap S (d S) hH hS (hd S hS)).
Qed.
