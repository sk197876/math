(** Measures on individual closed fan groups supporting Federer
    (1969), 2.8.20, p. 152; Saks1934 Lemma B
    (6)–(8), p. 258, and Cesari1939 Lemma III,
    p. 306. Later summation uses only the laws
    below. The small closed group comes from the sealed
    patch and the measure from the proved concentration laws.
    Source titles: VitaliMassObstruction.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  cardinality reals constructive_ereal topology.
From Federer Require Import ScalarPlaneRectangles ScalarHalfOpenRectangles ScalarMetricPlane
  BohrPatchUP BohrPatchLaws BohrPatchMeasure SquareBohrUnions
  HarmonicPrefixBounds MeasureUP MeasureBasic MetricDiameterUP MetricDiameter.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [is_bohr_group_measure]: abstract local
    large-average measure for the construction supporting Federer
    2.8.20, p. 152. The finite eligible cell family
    covers exactly the group; its area cost is explicit. *)
Record is_bohr_group_measure (R : realType) (U : set (scalar_metric_plane R))
    (cap p cost : R) (nu : set (scalar_metric_plane R) -> \bar R)
    (C : set (set (scalar_metric_plane R))) : Prop := {
  (** Source for [bohr_group_measure_law]: supporting measure
      law for Federer 2.8.20, p. 152. *)
  bohr_group_measure_law : is_measure nu;
  (** Source for [bohr_group_measure_measurable]: measurable
      eligible cells for Federer 2.8.20, p. 152. *)
  bohr_group_measure_measurable : forall S,
    measure_measurable (@scalar_plane_lebesgue R) S -> measure_measurable nu S;
  (** Source for [bohr_group_measure_finite]: finite rectangle
      group in Saks1934 Lemma B, p. 258, supporting
      Federer 2.8.20, p. 152. *)
  bohr_group_measure_finite : finite_set C;
  (** Source for [bohr_group_measure_rectangles]: nondegenerate
      closed eligible rectangles of Federer 2.8.20, p. 152. *)
  bohr_group_measure_rectangles : forall S, C S -> is_nondegenerate_scalar_rectangle S;
  (** Source for [bohr_group_measure_diameter]: small eligible
      cells in the supporting construction for Federer 2.8.20,
      p. 152; Saks1934 Lemma B (3), p. 258. *)
  bohr_group_measure_diameter : forall S, C S -> extended_metric_diameter S<=cap%:E;
  (** Source for [bohr_group_measure_mass]: large cell masses
      in Saks1934 Lemma B (8), p. 258, supporting
      Federer 2.8.20, p. 152. *)
  bohr_group_measure_mass : forall S, C S -> p%:E * scalar_plane_lebesgue S<=nu S;
  (** Source for [bohr_group_measure_union]: the exact finite
      group union for Federer 2.8.20, p. 152. *)
  bohr_group_measure_union : (\bigcup_(S in C) S)=U;
  (** Source for [bohr_group_measure_cost]: small total cost
      of one group in Saks1934 Lemma B (7), p. 258,
      supporting Federer 2.8.20, p. 152. *)
  bohr_group_measure_cost : nu setT<=cost%:E * scalar_plane_lebesgue U
}.

(** Source for [square_bohr_group_measure_exists]: existence
    of the local large-average measure used for Federer
    2.8.20, p. 152. It derives the group laws
    from abstract patch and concentration specifications, without
    computing through either private construction. *)
Theorem square_bohr_group_measure_exists (R : realType) r (cap p : R)
    (U : set (scalar_metric_plane R)) :
  (0<harmonic_partial_sum R r)%R -> (0<=p)%R -> is_square_bohr_union r cap U ->
  exists nu C, is_bohr_group_measure U cap p (p/harmonic_partial_sum R r)%R nu C.
Proof.
move=> hH hp0 [a [c [s [H [K [E [/andP [hs hcap] [hp hU]]]]]]]].
have [nu [hn [hmeas [hmass hcost]]]] := @bohr_patch_concentration_exists R
  (scalar_half_open_rectangle a (a+s)%R c (c+s)%R) r H K E p hp hH hp0.
pose C := K @` setT.
exists nu,C; constructor=> //.
- exact (@finite_image _ _ setT K (@finite_finset _ setT)).
- move=> S [i _ <-]; exact (@rectangle_companions_closed R (H i) (K i) (bohr_patch_companions hp i)).
- move=> S [i _ <-].
  have hsub := @bohr_patch_closed_union_subset R a (a+s)%R c (c+s)%R r H K E hp.
  have hKi : K i `<=` scalar_closed_rectangle a (a+s)%R c (c+s)%R.
    move=> x hx; apply: hsub; by exists i.
  apply: le_trans (@scalar_square_subset_diameter R a c s (K i) (ltW hs) hKi) _.
  by rewrite lee_fin.
- move=> S [i _ <-]; by rewrite hmass.
- rewrite hU; apply/seteqP; split=> [x [S [i _ <-] hx]|x [i _ hx]].
  + by exists i.
  + exists (K i)=> //; by exists i.
- apply: le_trans hcost _.
  apply: lee_wpmul2l; first by rewrite lee_fin divr_ge0 // ltW.
  rewrite hU; apply: (@measure_mono R [the choiceType of (R*R)%type] _ (scalar_plane_lebesgue_is_measure R)).
  move=> x [i _ hx]; exists i=> //.
  exact (@rectangle_companions_inclusion R (H i) (K i) (bohr_patch_companions hp i) x hx).
Qed.
