(** The local measure estimate supporting Federer (1969),
    2.8.20, p. 152; Saks1934 Lemma B (6)–(8),
    p. 258, and Cesari1939 Lemma III, p. 306.
    Concentrating the cell mass on the common core costs at
    most c/H times the patch-union area. Only the abstract
    patch and concentration laws are used. Source titles:
    VitaliMassObstruction.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal.
From Federer Require Import ScalarPlaneRectangles ScalarHalfOpenRectangles
  BohrPatchUP CoreConcentrationMeasure FiniteHalfOpenPartitionMeasure
  MeasureUP HarmonicPrefixBounds.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [bohr_patch_concentration_exists]: the local
    constant-density estimate in Saks1934 Lemma B (7)–(8),
    p. 258, supporting Federer 2.8.20, p. 152.
    A prescribed nonnegative multiplier c is attained on each
    eligible cell, at total cost at most c/H times the
    union area. This does not yet assert a fine covering. *)
Theorem bohr_patch_concentration_exists (R : realType) (Q : set (R*R)) r
    (H K : 'I_r -> set (R*R)) (E : set (R*R)) (c : R) :
  is_bohr_patch Q H K E -> (0<harmonic_partial_sum R r)%R -> (0<=c)%R ->
  exists nu : set (R*R) -> \bar R,
    is_measure nu /\
    (forall S, measure_measurable (@scalar_plane_lebesgue R) S -> measure_measurable nu S) /\
    (forall i, c%:E * scalar_plane_lebesgue (K i) = nu (K i)) /\
    nu setT <= (c/harmonic_partial_sum R r)%:E *
      scalar_plane_lebesgue (\bigcup_(i in @setT 'I_r) H i).
Proof.
move=> hp hH hc.
have hr : (0<r%:R :> R)%R by rewrite ltr0n; exact: bohr_patch_size hp.
have [hQpos hQfin] := positive_half_open_rectangle_area (bohr_patch_parent hp).
pose q := fine (scalar_plane_lebesgue Q).
have hq : scalar_plane_lebesgue Q = q%:E by rewrite /q fineK.
have hq0 : (0<=q)%R by apply: ltW; move: hQpos; rewrite hq lte_fin.
pose m := (c/r%:R*q)%R.
have hm : (0<=m)%R := mulr_ge0 (divr_ge0 hc (ltW hr)) hq0.
have hcore := bohr_patch_core hp.
have hEfin : scalar_plane_lebesgue E \is a fin_num.
  rewrite (ge0_fin_numE (measure_nonnegative (scalar_plane_lebesgue_is_measure R) E)).
  exact: nondegenerate_scalar_rectangle_finite hcore.
have [nu hn] := @core_concentration_exists R [the choiceType of (R*R)%type]
  (@scalar_plane_lebesgue R) E m (scalar_plane_lebesgue_is_measure R)
  (nondegenerate_scalar_rectangle_positive hcore) hEfin hm.
exists nu; split; first exact: core_concentration_measure hn.
split; first exact: core_concentration_measurable hn.
split.
- move=> i; rewrite (@core_concentration_containing R _ _ _ _ _ hn (K i)
    (bohr_patch_core_inclusion hp i)) (bohr_patch_cell_area hp i) hq -!EFinM /m mulrA.
  by [].
- rewrite (core_concentration_total hn).
  have hcH : (0<=c/harmonic_partial_sum R r)%R := divr_ge0 hc (ltW hH).
  have hcHE : (0 <= (c/harmonic_partial_sum R r)%:E)%E by rewrite lee_fin.
  have hb := lee_wpmul2l hcHE (bohr_patch_area_gain hp).
  apply: le_trans _ hb.
  rewrite hq -!EFinM.
  have he : ((c/harmonic_partial_sum R r)*(harmonic_partial_sum R r/r%:R)=c/r%:R)%R.
    by rewrite mulrA mulfVK ?gt_eqF.
  have he2 : ((c/harmonic_partial_sum R r)*(harmonic_partial_sum R r/r%:R*q)=m)%R.
    by rewrite (mulrA (c/harmonic_partial_sum R r)%R (harmonic_partial_sum R r/r%:R)%R q) he.
  by rewrite he2.
Qed.
