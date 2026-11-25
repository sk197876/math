(** Federer (1969), 4.1.23, p. 379:
    approximate each measurable step cell by a
    finite disjoint union of proper coordinate boxes.
    Every box closure lies inside the given
    open neighbourhood, so the later simplex hulls
    stay in the original compact target index. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  functions classical_sets reals constructive_ereal topology lra.
From Federer Require Import RealNormUP NormMetric InnerNorm InnerMetric
  GrassmannAbbreviations EuclideanInnerProduct EuclideanLebesgueDimensions
  EuclideanLebesgueBoxes EuclideanLebesgueCompactInner
  MeasureUP MeasureBasic MeasureSplit RadonCompactApproximation TopologicalBorel
  MetricOpenThickening MetricCompactNeighbourhood CompactEuclideanTubeExcess
  CompactOpenBoxApproximation FiniteDisjointOpenBoxFamilyUP
  FiniteDisjointOpenBoxVolume EuclideanOpenCoordinateBoxUP
  EuclideanClosedSupportTube VectorSetSum MeasureCompactCoreSetError.
From Federer Require Import HilbertFormCompactness.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [measurable_cell_box_approximation]: the
    suitable rectangular approximation in the proof
    of Federer 4.1.23, p. 379.
    The measurable cell stays inside its original
    compact carrier, all selected box closures lie
    in the prescribed open W, and both
    the symmetric-difference error and separate volume
    allowance tend to zero. Empty cells and
    ambient dimension zero remain included. *)
Theorem measurable_cell_box_approximation (R : realType) n
    (A K W : set (inner_metric_space (@euclidean_inner_productP R n)))
    (epsilon : R) :
  measure_measurable (@euclidean_lebesgue_measure R n) A ->
  compact K -> A `<=` K -> open W -> K `<=` W -> 0<epsilon ->
  exists (I : finType) (a b : I -> R_n R n)
    (G : I -> set (inner_metric_space (@euclidean_inner_productP R n))),
    is_finite_disjoint_open_box_family a b G /\
    (forall i, closure (G i) `<=` W) /\
    (@euclidean_lebesgue_measure R n (A `\` (\bigcup_i G i))+
      @euclidean_lebesgue_measure R n ((\bigcup_i G i) `\` A)<epsilon%:E)%E /\
    (@euclidean_lebesgue_measure R n (\bigcup_i G i)<=
      @euclidean_lebesgue_measure R n A+epsilon%:E)%E.
Proof.
move=> hA hK hAK hW hKW hEpsilon.
pose X := R_n R n.
pose E := inner_metric_space (@euclidean_inner_productP R n).
pose NX := inner_norm (@euclidean_inner_productP R n).
pose hNX := inner_norm_real_norm (@euclidean_inner_productP R n).
pose mu := @euclidean_lebesgue_measure R n.
pose hm := euclidean_lebesgue_is_measure R n.
pose eta := epsilon/4.
have hEta : 0<eta by rewrite /eta divr_gt0 // ltr0n.
have hThree : 3*eta<epsilon.
  have hSplit : epsilon= 4*eta by rewrite /eta mulrC divfK // pnatr_eq0.
  rewrite hSplit; lra.
have hEtaLe : eta<=epsilon by lra.
have hAFinite : (mu A< +oo)%E :=
  le_lt_trans (measure_mono hm hAK) (@euclidean_compact_finite R n K hK).
have [F [hF [hFA hAError]]] := @radon_compact_approximation R E mu hm
  (@euclidean_lebesgue_radon R n) A eta hA hAFinite hEta.
have hFMeas : measure_measurable mu F := @euclidean_borel_measurable R n F
  (closed_borel_set (compact_closed (@metric_hausdorff R E) hF)).
case: (pselect (F !=set0))=> hNonempty.
- have [d [hD hExcess]] := @compact_euclidean_tube_excess_small R n F eta hF hEta.
  have [margin [hMargin hMarginTube]] := @compact_metric_open_thickening R E K W hK hW hKW.
  pose r := Num.min d (margin/2).
  have hHalf : 0<margin/2 by rewrite divr_gt0 // ltr0n.
  have hR : 0<r by rewrite /r lt_min hD hHalf.
  have hRD : r<=d by rewrite /r ge_min lexx.
  have hRM : r<=margin/2 by rewrite /r ge_min lexx orbT.
  have hHalfSmall : margin/2<margin by lra.
  have [I [a [b [G [hFamily [_ [hLower hNear]]]]]]] :=
    @compact_open_box_approximation_exists R n F r hF hNonempty hR.
  pose H := \bigcup_i G i.
  have hHMeas : measure_measurable mu H :=
    @finite_disjoint_open_box_union_measurable R n I a b G hFamily.
  have hHExcess : (mu (H `\` F)<eta%:E)%E.
    apply: (le_lt_trans _ hExcess); apply: (measure_mono hm)=> x [hx hNotF].
    split; last exact: hNotF.
    have [y hy hDistance] := @hNear x hx.
    exists y; first exact: hy.
    exact: lt_le_trans hDistance hRD.
  pose Tube : set E := @euclidean_closed_support_tube R n K (margin/2).
  have hTubeClosed : closed Tube := compact_closed (@metric_hausdorff R E)
    (@euclidean_closed_support_tube_compact R n K (margin/2) hK).
  have hHTube : H `<=` Tube.
    move=> x hx; have [y hy hDistance] := @hNear x hx.
    apply/vector_set_sum_membership; exists y,(x-y); split.
    + exact: (@hAK y (@hFA y hy)).
    split.
    + change (is_true (NX (x-y)<=margin/2)).
      have hNorm : NX (x-y)=NX (y-x) := real_seminorm_subtract hNX.1 x y.
      rewrite hNorm.
      change (is_true (NX (y-x)<r)) in hDistance.
      exact: le_trans (ltW hDistance) hRM.
    + by rewrite addrC subrK.
  have hTubeW : Tube `<=` W.
    move=> x /vector_set_sum_membership [y [z [hy [hz ->]]]].
    apply: hMarginTube; exists y; first exact: hy.
    change (is_true (NX (y-(y+z))<margin)).
    rewrite opprD addrA subrr add0r /NX inner_normN.
    exact: le_lt_trans hz hHalfSmall.
  have hClosures i : closure (G i) `<=` W.
    apply: (subset_trans _ hTubeW).
    rewrite ((closure_id Tube).1 hTubeClosed); apply: closureS=> x hx.
    apply: hHTube; by exists i.
  have [_ [hError hMass]] := @measure_compact_core_set_error R E mu hm
    A F H eta hA hFMeas hHMeas hAFinite hFA hEta hAError hHExcess hLower.
  exists I,a,b,G; split; first exact: hFamily.
  split; first exact: hClosures.
  split.
  + apply: (lt_trans hError); by rewrite lte_fin.
  + apply: (le_trans (ltW hMass)); apply: leeD; first exact: lexx.
    by rewrite lee_fin.
- have hEmpty : F=set0.
    apply: funext=> x; apply: propext; split; last by move=> [].
    move=> hx; exfalso; apply: hNonempty; by exists x.
  have hError : (mu A<epsilon%:E)%E.
    rewrite hEmpty setD0 in hAError.
    apply: (lt_le_trans hAError); by rewrite lee_fin.
  pose I : finType := [the finType of 'I_0].
  pose a := fun _ : I => (0 : X).
  pose G := fun _ : I => (set0 : set E).
  have hI (i : I) : False by have := ltn_ord i; rewrite ltn0.
  have hFamily : is_finite_disjoint_open_box_family a a G.
    constructor; [by move=> i; case: (hI i)|by move=> i; case: (hI i)].
  have hUnion : (\bigcup_i G i)=set0.
    apply: funext=> x; apply: propext; split; last by move=> [].
    move=> [i _ _]; exact: hI i.
  exists I,a,a,G; split; first exact: hFamily.
  split; first by move=> i; case: (hI i).
  rewrite hUnion setD0 set0D (measure_empty hm) adde0.
  split; first exact: hError.
  apply: adde_ge0.
  - exact: measure_nonnegative hm A.
  - by rewrite lee_fin; exact: ltW hEpsilon.
Qed.
