(** Private placement construction supporting Federer (1969),
    2.8.20, p. 152; Saks1934 Lemma B, pp. 258–259,
    and Cesari1939 Lemma III, pp. 306–307. Positive
    coordinate changes place the normalized witness in any
    remaining rectangle. Disjoint strip areas prove the gain;
    half-open companions make the remaining regions exact.
    Later arguments must use the sealed patch laws, not these
    coordinates. Source titles: VitaliMassObstruction.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  cardinality reals constructive_ereal.
From mathcomp Require Import ring lra.
From Federer Require Import ScalarPlaneRectangles ScalarHalfOpenRectangles
  ScalarRectangleAffine BohrFanConstruction BohrPatchUP HarmonicPrefixBounds
  MeasureUP MeasureBasic MeasureDisjointSupport NonnegativeSum FiniteCoverMeasureBounds.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [placed_bohr_strip_gain]: private placement
    of the disjoint strips supporting Federer 2.8.20,
    p. 152; Cesari1939 Lemma III, p. 306.
    Only individual rectangle area formulas are used. *)
Lemma placed_bohr_strip_gain (R : realType) r (a w c h : R) :
  (0<r)%N -> (0<w)%R -> (0<h)%R ->
  ((harmonic_partial_sum R r / r%:R)*(w*h))%:E <=
    scalar_plane_lebesgue (\bigcup_(i in @setT 'I_r)
      rectangle_affine_map a w c h @` @bohr_fan_cell_witness R r i).
Proof.
move=> hr hw hh.
pose f := rectangle_affine_map a w c h.
pose F i := f @` @bohr_fan_strip_witness R r i.
pose U := \bigcup_(i in @setT 'I_r) f @` @bohr_fan_cell_witness R r i.
have hf : injective f := can_inj (rectangle_affine_cancel a c hw hh).
have harea i : scalar_plane_lebesgue (F i) =
    ((w*h)*((r%:R : R)^-1*(i.+1%:R)^-1))%:E.
  rewrite /F /f /bohr_fan_strip_witness rectangle_affine_strip_area //.
  - by rewrite -/(@bohr_fan_strip_witness R r i) bohr_fan_strip_witness_area // -EFinM.
  - by rewrite add0r ler_pM2r ?invr_gt0 ?ltr0n // ler_nat leqnSn.
  - by rewrite invr_ge0 ler0n.
have hb : nonnegative_sum setT (fun i => scalar_plane_lebesgue (F i)) <= scalar_plane_lebesgue U.
  apply: (@measure_disjoint_sum_bound R [the choiceType of (R*R)%type] [the choiceType of 'I_r]
    (@scalar_plane_lebesgue R) (scalar_plane_lebesgue_is_measure R) U setT F).
  - move=> i _ x [y hy <-]; exists i=> //; exists y=> //.
    exact: bohr_fan_strip_within_cell hy.
  - move=> i _; rewrite /F /f /bohr_fan_strip_witness rectangle_affine_strip_image //.
    exact: scalar_half_open_strip_measurable.
  - move=> i j _ _ hne; apply/seteqP; split=> [x [[y hy he] [z hz he']]|x []].
    have heyz : y=z := hf y z (eq_trans he (esym he')).
    have hd := @bohr_fan_strips_disjoint R r hr i j hne.
    have ht : (@bohr_fan_strip_witness R r i `&` @bohr_fan_strip_witness R r j) y.
      split=> //; by rewrite heyz.
    by rewrite hd in ht.
have he : nonnegative_sum setT (fun i => scalar_plane_lebesgue (F i)) =
    (((w*h)*(r%:R : R)^-1)*harmonic_partial_sum R r)%:E.
  rewrite (@finite_type_nonnegative_sum R [the finType of 'I_r] _
    (fun i => measure_nonnegative (scalar_plane_lebesgue_is_measure R) (F i))).
  under eq_bigr do rewrite harea mulrA.
  by rewrite sumEFin -mulr_sumr -harmonic_partial_sumE.
move: hb; rewrite he; have -> : (((w*h)*(r%:R : R)^-1)*harmonic_partial_sum R r =
    (harmonic_partial_sum R r/r%:R)*(w*h))%R by ring.
by [].
Qed.

(** Source for [bohr_patch_on_coordinate_rectangle]: private
    existence of a local patch supporting Federer 2.8.20,
    p. 152; Saks1934 Lemma B, p. 258.
    Both side lengths and the finite fan index are positive. *)
Lemma bohr_patch_on_coordinate_rectangle (R : realType) r (a w c h : R) :
  (0<r)%N -> (0<w)%R -> (0<h)%R ->
  exists (H K : 'I_r -> set (R*R)) E,
    is_bohr_patch (scalar_half_open_rectangle a (a+w) c (c+h)) H K E.
Proof.
move=> hr hw hh.
pose u (i : 'I_r) := (i.+1%:R/r%:R : R)%R.
pose v (i : 'I_r) := ((i.+1%:R : R)^-1)%R.
pose H i := scalar_half_open_rectangle a (a+w*u i) c (c+h*v i).
pose f := rectangle_affine_map a w c h.
pose K i := f @` @bohr_fan_cell_witness R r i.
pose E := f @` @bohr_fan_core_witness R r.
have hrR : (0<r%:R :> R)%R by rewrite ltr0n.
have hu i : (0<u i)%R by rewrite /u divr_gt0 ?ltr0n.
have hv i : (0<v i)%R by rewrite /v invr_gt0 ltr0n.
have hu1 i : (u i<=1)%R by rewrite /u ler_pdivrMr // mul1r ler_nat.
have hv1 i : (v i<=1)%R by rewrite /v invf_le1 ?ltr0n // ler1n.
have ha i : (a<a+w*u i)%R by rewrite ltrDl mulr_gt0.
have hc i : (c<c+h*v i)%R by rewrite ltrDl mulr_gt0.
have hK i : K i = scalar_closed_rectangle a (a+w*u i) c (c+h*v i).
  by rewrite /K /f /bohr_fan_cell_witness rectangle_affine_closed_image //
    !mulr0 !addr0.
have haw : (a<=a+w)%R by lra.
have hch : (c<=c+h)%R by lra.
exists H,K,E; constructor.
- exists a,(a+w)%R,c,(c+h)%R; split; first by rewrite ltrDl.
  split=> //; by rewrite ltrDl.
- exact hr.
- move=> i; exists a,(a+w*u i)%R,c,(c+h*v i)%R; split=> //; split=> //; split=> //; exact: hK.
- move=> i [x y]; rewrite /H /scalar_half_open_rectangle /= !in_itv /=.
  move=> [/andP [hx1 hx2] /andP [hy1 hy2]]; split; apply/andP; split=> //.
  + apply: lt_le_trans hx2 _; rewrite lerD2l -{2}(mulr1 w) ler_pM2l //.
  + apply: lt_le_trans hy2 _; rewrite lerD2l -{2}(mulr1 h) ler_pM2l //.
- move=> [x y] [hxy hlow] i.
  have hbase : scalar_half_open_rectangle a (a+w) c (c+h) (a,c).
    rewrite /scalar_half_open_rectangle /= !in_itv /= !lexx /=.
    by rewrite ltrDl hw ltrDl hh.
  have [hxlo hylo] := hlow (a,c) hbase.
  move: hxy; rewrite /scalar_half_open_rectangle /= !in_itv /=.
  move=> [/andP [hxhi _] /andP [hyhi _]].
  have -> : x=a by apply/eqP; rewrite eq_le hxlo hxhi.
  have -> : y=c by apply/eqP; rewrite eq_le hylo hyhi.
  rewrite hK /scalar_closed_rectangle /= !in_itv /= !lexx /=.
  by rewrite (ltW (ha i)) (ltW (hc i)).
- rewrite /E /f /bohr_fan_core_witness rectangle_affine_closed_image // !mulr0 !addr0.
  have hn : (0<(r%:R : R)^-1)%R by rewrite invr_gt0.
  exists a,(a+w*(r%:R)^-1)%R,c,(c+h*(r%:R)^-1)%R.
  split; first by rewrite ltrDl mulr_gt0.
  split=> //; by rewrite ltrDl mulr_gt0.
- move=> i x [y hy <-]; exists y=> //; exact (@bohr_fan_core_within_cells R r i hr y hy).
- move=> i; rewrite /K /f /bohr_fan_cell_witness rectangle_affine_closed_area //.
  + rewrite -/(@bohr_fan_cell_witness R r i) bohr_fan_cell_witness_area //.
    rewrite scalar_half_open_rectangle_value //.
    by rewrite addrAC subrr add0r addrAC subrr add0r muleC.
  + exact: ltW (hu i).
  + exact: ltW (hv i).
- have hg := @placed_bohr_strip_gain R r a w c h hr hw hh.
  have hU : scalar_plane_lebesgue (\bigcup_(i in @setT 'I_r) K i) =
      scalar_plane_lebesgue (\bigcup_(i in @setT 'I_r) H i).
    have hKfun : K = (fun i => scalar_closed_rectangle a (a+w*u i) c (c+h*v i)).
      exact: funext hK.
    rewrite hKfun /H; apply: finite_closed_half_open_union_area;
      move=> i; exact: ltW (ha i) || exact: ltW (hc i).
  rewrite scalar_half_open_rectangle_value //.
  have he : ((a+w-a)*(c+h-c)=w*h)%R by ring.
  by rewrite he -EFinM -hU.
Qed.

(** Source for [bohr_patch_exists]: existence for an abstract
    positive half-open parent, supporting Federer 2.8.20,
    p. 152. Coordinate choices occur only in this
    opaque construction proof; later packing uses the patch laws. *)
Theorem bohr_patch_exists (R : realType) r (Q : set (R*R)) :
  (0<r)%N -> is_nondegenerate_half_open_rectangle Q ->
  exists (H K : 'I_r -> set (R*R)) E, is_bohr_patch Q H K E.
Proof.
move=> hr [a [b [c [d [hab [hcd ->]]]]]].
have hw : (0<b-a)%R by rewrite subr_gt0.
have hh : (0<d-c)%R by rewrite subr_gt0.
have [H [K [E hp]]] := @bohr_patch_on_coordinate_rectangle R r a (b-a)%R c (d-c)%R hr hw hh.
have he1 : (a+(b-a)=b)%R by ring.
have he2 : (c+(d-c)=d)%R by ring.
by rewrite he1 he2 in hp; exists H,K,E.
Qed.

(** Source for [bohr_patch_data_exists]: bundled existence
    for opaque sealing of the local finite group supporting
    Federer 2.8.20, p. 152. No coordinate formula
    is part of the exported data laws. *)
Theorem bohr_patch_data_exists (R : realType) r (Q : set (R*R)) :
  (0<r)%N -> is_nondegenerate_half_open_rectangle Q ->
  exists p : (('I_r -> set (R*R))*('I_r -> set (R*R)))*set (R*R),
    is_bohr_patch Q p.1.1 p.1.2 p.2.
Proof.
move=> hr hQ; have [H [K [E hp]]] := @bohr_patch_exists R r Q hr hQ.
by exists (H,K,E).
Qed.
