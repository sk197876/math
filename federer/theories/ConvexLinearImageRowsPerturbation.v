(** Expanded continuity support for Federer (1969), 3.2.45,
    p. 279: add the relative row-volume bounds while replacing
    the rows of one linear map by those of another. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology ring.
From Federer Require Import GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct InnerMetric InnerNorm InnerConvex
  EuclideanRowFamily ConvexLinearImageRowPerturbation LinearImageUnitRowsBound
  CompactConvexProjectedGaugeFinite ProjectedVolumeGauge EuclideanLebesgueDimensions
  MeasureUP FiniteUniformChainIncrement.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [convex_linear_image_rows_perturbation]: an expanded
    support theorem for the exponent continuity assertion of
    Federer 3.2.45, p. 279. Replace each actual scalar row
    in turn. The already proved single-row bound gives total
    error at most (m+1) delta times the source's own projection
    supremum. Every finite part below is justified by the proved
    compact-convex finiteness; no positive volume is required. *)
Theorem convex_linear_image_rows_perturbation (R : realType) n m
    (K : set (inner_metric_space (@euclidean_inner_productP R n)))
    (v w : 'I_m.+1 -> R_n R n)
    (F G : {linear R_n R n -> R_n R m.+1}) (delta : R) :
  (m.+1 <= n)%N -> compact K -> is_inner_convex K ->
  is_euclidean_row_family v F -> is_euclidean_row_family w G ->
  (forall i, (inner_norm (@euclidean_inner_productP R n) (v i) <= 1)%R) ->
  (forall i, (inner_norm (@euclidean_inner_productP R n) (w i) <= 1)%R) ->
  (forall i, (inner_norm (@euclidean_inner_productP R n) (v i-w i) <= delta)%R) ->
  @euclidean_lebesgue_measure R m.+1 (F @` K) <=
    euclidean_lebesgue_measure m.+1 (G @` K) +
      ((m.+1%:R * delta)%R)%:E * @projected_volume_gauge R n m.+1 K.
Proof.
move=> hMN hCompact hConvex hV hW hNormV hNormW hDifference.
pose r (j : nat) (i : 'I_m.+1) : R_n R n := if (i < j)%N then v i else w i.
have hExists j : exists L : {linear R_n R n -> R_n R m.+1}, is_euclidean_row_family (r j) L.
  exact: euclidean_row_family_exists.
have [L hL] := choice hExists.
have hNorm j i : (inner_norm (@euclidean_inner_productP R n) (r j i) <= 1)%R.
  rewrite /r; case: (i < j)%N; [exact: hNormV | exact: hNormW].
pose C := @projected_volume_gauge R n m.+1 K.
pose c : R := fine C.
have hCValue : C = c%:E := @compact_convex_projected_gauge_finite_value R n m.+1 hMN K hCompact hConvex.
have hCFinite : C < +oo := @compact_convex_projected_gauge_finite R n m.+1 hMN K hCompact hConvex.
pose a (j : nat) : R := fine (@euclidean_lebesgue_measure R m.+1 (L j @` K)).
have hValue j : @euclidean_lebesgue_measure R m.+1 (L j @` K) = (a j)%:E.
  symmetry; apply: fineK.
  rewrite (ge0_fin_numE (measure_nonnegative (euclidean_lebesgue_is_measure R m.+1) _)).
  apply: le_lt_trans _ hCFinite.
  exact: (@linear_image_unit_rows_projected_volume_bound R n m.+1 (r j) (L j) K hMN (hL j) (hNorm j)).
have hStep j (hJ : (j < m.+1)%N) : (a j.+1 <= a j + delta*c)%R.
  pose i : 'I_m.+1 := Ordinal hJ.
  have hCommon (u : 'I_m.+1) (hU : u != i) : r j.+1 u = r j u.
    have hNat : (val u != j)%N.
      apply/eqP=> hEqual; apply: (elimN eqP hU).
      apply: val_inj; exact hEqual.
    by rewrite /r ltnS leq_eqVlt (negbTE hNat).
  have hOther u (hU : u != i) : (inner_norm (@euclidean_inner_productP R n) (r j.+1 u) <= 1)%R.
    exact: hNorm.
  have hDiff : (inner_norm (@euclidean_inner_productP R n) (r j.+1 i-r j i) <= delta)%R.
    rewrite /r /i /= ltnSn ltnn; exact: hDifference.
  have hVolume := @convex_linear_image_one_row_perturbation R n m K
    (r j.+1) (r j) (L j.+1) (L j) i delta hMN hCompact hConvex
    (hL j.+1) (hL j) hCommon hOther hDiff.
  by rewrite hValue hValue -/C hCValue -EFinM -EFinD lee_fin in hVolume.
have hChain := @finite_uniform_chain_increment R a (delta*c)%R m.+1 hStep.
have hStart : L 0%N @` K = G @` K.
  apply: eq_imagel=> x _; apply/ffunP=> i.
  by rewrite (hL 0%N) /r ltn0 hW.
have hEnd : L m.+1 @` K = F @` K.
  apply: eq_imagel=> x _; apply/ffunP=> i.
  by rewrite (hL m.+1) /r (ltn_ord i) hV.
have hStartValue := hValue 0%N; rewrite hStart in hStartValue.
have hEndValue := hValue m.+1; rewrite hEnd in hEndValue.
rewrite hEndValue hStartValue -/C hCValue -EFinM -EFinD lee_fin.
have hEquality : (a 0%N + m.+1%:R * (delta*c) = a 0%N + (m.+1%:R*delta)*c)%R by ring.
by rewrite hEquality in hChain.
Qed.
