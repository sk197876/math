(** Private existence construction for the finite rectangular
    fans supporting Federer (1969), 2.8.20, p. 152.
    The concrete normalized cells have width (i+1)/r and
    height 1/(i+1). Disjoint vertical strips establish the
    harmonic area gain. This expands the finite-group geometry
    of Saks1934 Lemma B, p. 258, and the harmonic
    parameter choice in Cesari1939 Lemma III, p. 306.
    Only the existence result and its sealed specification
    are intended for downstream use. Specification and exact
    source titles: BohrFanUP.v and VitaliMassObstruction.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets cardinality reals constructive_ereal.
From Federer Require Import ScalarPlaneRectangles BohrFanUP HarmonicPrefixBounds
  MeasureUP MeasureBasic MeasureDisjointSupport NonnegativeSum FiniteCoverMeasureBounds.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [bohr_fan_cell_witness]: one concrete cell
    in the supporting finite-group construction for Federer
    2.8.20, p. 152; Saks1934 Lemma B, p. 258.
    The implementation is confined to this construction module. *)
Definition bohr_fan_cell_witness (R : realType) r (i : 'I_r) :=
  scalar_closed_rectangle (0 : R) (i.+1%:R / r%:R) 0 (i.+1%:R)^-1.

(** Source for [bohr_fan_strip_witness]: private disjoint
    vertical strip inside a fan cell, supporting the harmonic
    gain for Federer 2.8.20, p. 152, and the
    parameter choice in Cesari1939 Lemma III, p. 306. *)
Definition bohr_fan_strip_witness (R : realType) r (i : 'I_r) :=
  scalar_half_open_strip (0 + i%:R / r%:R : R) (i.+1%:R / r%:R) 0 (i.+1%:R)^-1.

(** Source for [bohr_fan_cell_witness_area]: the equal-area
    clause of the fan specification supporting Federer
    2.8.20, p. 152; Saks1934 (4), p. 258. *)
Lemma bohr_fan_cell_witness_area (R : realType) r (i : 'I_r) :
  (0 < r)%N -> scalar_plane_lebesgue (@bohr_fan_cell_witness R r i) = ((r%:R : R)^-1)%:E.
Proof.
move=> hr.
have hrR : (0 < r%:R :> R)%R by rewrite ltr0n.
have hiR : (0 < i.+1%:R :> R)%R by rewrite ltr0n.
by rewrite /bohr_fan_cell_witness scalar_closed_rectangle_value
  ?divr_ge0 ?invr_ge0 ?ler0n // !subr0 mulrAC mulfV ?gt_eqF // mul1r.
Qed.

(** Source for [bohr_fan_strip_witness_area]: the disjoint
    strip areas used for the supporting fan gain in Federer
    2.8.20, p. 152; Cesari1939 Lemma III, p. 306. *)
Lemma bohr_fan_strip_witness_area (R : realType) r (i : 'I_r) :
  (0 < r)%N -> scalar_plane_lebesgue (@bohr_fan_strip_witness R r i) =
    (((r%:R : R)^-1) * (i.+1%:R)^-1)%:E.
Proof.
move=> hr.
have hrR : (0 < r%:R :> R)%R by rewrite ltr0n.
have hwidth : (0 + i%:R/r%:R <= i.+1%:R/r%:R :> R)%R.
  by rewrite add0r ler_pM2r ?invr_gt0 // ler_nat leqnSn.
have hw : (i.+1%:R/r%:R - i%:R/r%:R = (r%:R : R)^-1)%R.
  by rewrite -mulrBl -addn1 natrD addrAC subrr add0r mul1r.
by rewrite /bohr_fan_strip_witness scalar_half_open_strip_value // ?invr_ge0 ?ler0n //
  add0r hw subr0.
Qed.

(** Source for [bohr_fan_strip_within_cell]: private strip
    containment supporting the fan-union area estimate for
    Federer 2.8.20, p. 152; Saks1934 Lemma B,
    p. 258. The closed eligible cell includes the strip's
    open right boundary convention. *)
Lemma bohr_fan_strip_within_cell (R : realType) r (i : 'I_r) :
  @bohr_fan_strip_witness R r i `<=` @bohr_fan_cell_witness R r i.
Proof.
move=> [x y]; rewrite /bohr_fan_strip_witness /bohr_fan_cell_witness
  /scalar_half_open_strip /scalar_closed_rectangle /= !in_itv /=.
move=> [/andP [hx1 hx2] hy]; split=> //; apply/andP; split; last exact: ltW hx2.
apply: le_trans _ hx1; rewrite add0r divr_ge0 ?ler0n //.
Qed.

(** Source for [bohr_fan_strip_index_gap]: private index
    comparison for disjoint vertical strips supporting Federer
    2.8.20, p. 152. The right endpoint of an
    earlier strip is at most the next strip's left endpoint. *)
Lemma bohr_fan_strip_index_gap (R : realType) r (i j : 'I_r) :
  (0 < r)%N -> (i < j)%N -> (i.+1%:R/r%:R <= j%:R/r%:R :> R)%R.
Proof.
move=> hr hij; rewrite ler_pM2r ?invr_gt0 ?ltr0n // ler_nat; exact hij.
Qed.

(** Source for [bohr_fan_strips_disjoint]: private disjointness
    of the vertical strips for the supporting fan-volume bound
    in Federer 2.8.20, p. 152. No area boundary
    convention is needed because the first factor is half-open. *)
Lemma bohr_fan_strips_disjoint (R : realType) r :
  (0 < r)%N -> forall i j : 'I_r, i <> j ->
  @bohr_fan_strip_witness R r i `&` @bohr_fan_strip_witness R r j = set0.
Proof.
move=> hr i j hne; apply/seteqP; split=> [[x y] [hi hj]|z []].
have /andP [hil hiu] : (0 + i%:R/r%:R <= x < i.+1%:R/r%:R)%R := hi.1.
have /andP [hjl hju] : (0 + j%:R/r%:R <= x < j.+1%:R/r%:R)%R := hj.1.
rewrite add0r in hil.
rewrite add0r in hjl.
case: (ltngtP (val i) (val j))=> hij.
- have hbad := lt_le_trans hiu (le_trans (bohr_fan_strip_index_gap R hr hij) hjl).
  by rewrite ltxx in hbad.
- have hbad := lt_le_trans hju (le_trans (bohr_fan_strip_index_gap R hr hij) hil).
  by rewrite ltxx in hbad.
- exfalso; apply: hne; exact: val_inj hij.
Qed.

(** Source for [bohr_fan_cell_witness_rectangle]: nondegeneracy
    and normalized containment for the finite group supporting
    Federer 2.8.20, p. 152; Saks1934 Lemma B,
    p. 258. All coordinate upper endpoints are positive. *)
Lemma bohr_fan_cell_witness_rectangle (R : realType) r (i : 'I_r) :
  (0 < r)%N -> is_nondegenerate_scalar_rectangle (@bohr_fan_cell_witness R r i) /\
    @bohr_fan_cell_witness R r i `<=` scalar_closed_rectangle (0 : R) 1 0 1.
Proof.
move=> hr.
have hrR : (0 < r%:R :> R)%R by rewrite ltr0n.
have hiR : (0 < i.+1%:R :> R)%R by rewrite ltr0n.
have hw : (0 < i.+1%:R/r%:R :> R)%R by rewrite divr_gt0.
have hh : (0 < (i.+1%:R : R)^-1)%R by rewrite invr_gt0.
have hwu : (i.+1%:R/r%:R <= 1 :> R)%R.
  by rewrite ler_pdivrMr // mul1r ler_nat.
have hhu : ((i.+1%:R : R)^-1 <= 1)%R by rewrite invf_le1 // ler1n.
split.
- exists (0 : R)%R,(i.+1%:R/r%:R : R)%R,(0 : R)%R,((i.+1%:R : R)^-1)%R; by split=> //; split.
- move=> [x y]; rewrite /bohr_fan_cell_witness /scalar_closed_rectangle /= !in_itv /=.
  move=> [/andP [hx0 hxi] /andP [hy0 hyi]]; split; apply/andP; split=> //.
  + exact: le_trans hxi hwu.
  + exact: le_trans hyi hhu.
Qed.

(** Source for [bohr_fan_core_witness]: a concrete common
    positive rectangular core in the construction supporting
    Federer 2.8.20, p. 152; Saks1934 (6), p. 258.
    This implementation is private to the witness proof. *)
Definition bohr_fan_core_witness (R : realType) r :=
  scalar_closed_rectangle (0 : R) (r%:R)^-1 0 (r%:R)^-1.

(** Source for [bohr_fan_core_witness_rectangle]: positivity
    of the common-core area supporting Federer 2.8.20,
    p. 152; Saks1934 (6), p. 258. The core
    is nondegenerate whenever the fan index is positive. *)
Lemma bohr_fan_core_witness_rectangle (R : realType) r :
  (0 < r)%N -> is_nondegenerate_scalar_rectangle (@bohr_fan_core_witness R r).
Proof.
move=> hr; have hi : (0 < (r%:R : R)^-1)%R by rewrite invr_gt0 ltr0n.
exists (0 : R)%R,((r%:R : R)^-1)%R,(0 : R)%R,((r%:R : R)^-1)%R; by split=> //; split.
Qed.

(** Source for [bohr_fan_core_within_cells]: the common-core
    inclusions supporting Federer 2.8.20, p. 152;
    Saks1934 (6), p. 258. Reciprocal monotonicity supplies
    the vertical bound; the first horizontal width is smallest. *)
Lemma bohr_fan_core_within_cells (R : realType) r (i : 'I_r) :
  (0 < r)%N -> @bohr_fan_core_witness R r `<=` @bohr_fan_cell_witness R r i.
Proof.
move=> hr.
have hrR : (0 < r%:R :> R)%R by rewrite ltr0n.
have hiR : (0 < i.+1%:R :> R)%R by rewrite ltr0n.
have hinv : (0 <= (r%:R : R)^-1)%R by rewrite invr_ge0 ler0n.
have hw : ((r%:R : R)^-1 <= i.+1%:R/r%:R)%R.
  have h1 : (1 <= i.+1%:R :> R)%R by rewrite ler1n.
  have h := ler_wpM2r hinv h1; by rewrite mul1r in h.
have hh : ((r%:R : R)^-1 <= (i.+1%:R : R)^-1)%R.
  by rewrite (@lef_pV2 R _ _ hrR hiR) ler_nat.
move=> [x y]; rewrite /bohr_fan_core_witness /bohr_fan_cell_witness /scalar_closed_rectangle /= !in_itv /=.
move=> [/andP [hx0 hxi] /andP [hy0 hyi]]; split; apply/andP; split=> //.
- exact: le_trans hxi hw.
- exact: le_trans hyi hh.
Qed.

(** Source for [bohr_fan_witness_harmonic_gain]: the private
    strip-sum proof of the harmonic gain supporting Federer
    2.8.20, p. 152, and the finite parameter choice
    in Cesari1939 Lemma III, p. 306. Distinct strips
    are disjoint and lie in the union of the closed cells. *)
Lemma bohr_fan_witness_harmonic_gain (R : realType) r :
  (0 < r)%N -> (harmonic_partial_sum R r / r%:R)%:E <=
    scalar_plane_lebesgue (\bigcup_(i in @setT 'I_r) @bohr_fan_cell_witness R r i).
Proof.
move=> hr.
pose F := fun i : 'I_r => @bohr_fan_strip_witness R r i.
pose U := \bigcup_(i in @setT 'I_r) @bohr_fan_cell_witness R r i.
have hb : nonnegative_sum setT (fun i => scalar_plane_lebesgue (F i)) <= scalar_plane_lebesgue U.
  apply: (@measure_disjoint_sum_bound R [the choiceType of (R*R)%type] [the choiceType of 'I_r]
    (@scalar_plane_lebesgue R) (scalar_plane_lebesgue_is_measure R) U setT F).
  - move=> i _ x hx; exists i=> //; exact: bohr_fan_strip_within_cell hx.
  - move=> i _; exact: scalar_half_open_strip_measurable.
  - move=> i j _ _ hne; exact (@bohr_fan_strips_disjoint R r hr i j hne).
have he : nonnegative_sum setT (fun i => scalar_plane_lebesgue (F i)) =
    (((r%:R : R)^-1) * harmonic_partial_sum R r)%:E.
  rewrite (@finite_type_nonnegative_sum R [the finType of 'I_r] _
    (fun i => measure_nonnegative (scalar_plane_lebesgue_is_measure R) (F i))).
  under eq_bigr do rewrite /F bohr_fan_strip_witness_area //.
  by rewrite sumEFin -mulr_sumr -harmonic_partial_sumE.
by move: hb; rewrite he mulrC.
Qed.

(** Source for [bohr_fan_exists]: existence of a finite
    fan satisfying the abstract laws supporting Federer
    2.8.20, p. 152; Saks1934 Lemma B, p. 258,
    and Cesari1939 Lemma III, p. 306. The explicit
    cell and core constructions remain inside this opaque proof. *)
Theorem bohr_fan_exists (R : realType) r : (0 < r)%N ->
  exists (F : 'I_r -> set (R*R)) E, is_bohr_fan F E.
Proof.
move=> hr; exists (@bohr_fan_cell_witness R r), (@bohr_fan_core_witness R r); constructor.
- exact hr.
- move=> i; exact: bohr_fan_cell_witness_rectangle hr.
- move=> i; exact: bohr_fan_cell_witness_area hr.
- exact: bohr_fan_core_witness_rectangle hr.
- move=> i; exact: bohr_fan_core_within_cells hr.
- exact: bohr_fan_witness_harmonic_gain hr.
Qed.

(** Source for [bohr_fan_pair_exists]: paired form of the
    proved witness supporting Federer 2.8.20, p. 152,
    for opaque sealing. It carries precisely the fan and
    common core, without exposing their coordinate formulas. *)
Theorem bohr_fan_pair_exists (R : realType) r : (0 < r)%N ->
  exists w : ('I_r -> set (R*R)) * set (R*R), is_bohr_fan w.1 w.2.
Proof.
move=> hr; have [F [E h]] := @bohr_fan_exists R r hr.
by exists (F,E).
Qed.
