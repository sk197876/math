(** Federer (1969), 3.2.18, p. 255:
    find one global Lipschitz parametrization
    meeting a positive-mass remainder. Use the
    finite approximation assertion of 3.2.14
    before the Borel injective-piece reduction. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology lra.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric
  RectifiableSetUP RectifiableFiniteApproximation EuclideanRectifiableGlobalParametrization
  LipschitzUP HausdorffMeasure HausdorffClosedCoverAgreement
  MeasureUP MeasureBasic MeasureSplit BorelRegularMeasureUP TopologicalBorel.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [rectifiable_positive_global_parametrization]:
    the first reduction through 3.2.14
    in Federer 3.2.18, p. 255.
    A positive subset of W meets one
    globally Lipschitz image in positive Hausdorff
    mass, with no source-domain measurability premise. *)
Theorem rectifiable_positive_global_parametrization (R : realType) m n
    (W A : set (inner_metric_space (@euclidean_inner_productP R n))) :
  is_measure_m_rectifiable (@hausdorff_measure R
    (inner_metric_space (@euclidean_inner_productP R n)) m.+1) m.+1 W ->
  A `<=` W -> (0<@hausdorff_measure R
    (inner_metric_space (@euclidean_inner_productP R n)) m.+1 A)%E ->
  exists f : inner_metric_space (@euclidean_inner_productP R m.+1) ->
      inner_metric_space (@euclidean_inner_productP R n),
    is_metric_lipschitz setT f /\
    (0<@hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R n)) m.+1
      (A `&` (f @` setT)))%E.
Proof.
move=> hW hAW hPos.
pose Y := inner_metric_space (@euclidean_inner_productP R n).
pose mu := @hausdorff_measure R Y m.+1.
have hm := @hausdorff_measure_is_measure R Y m.+1.
have hReg := @hausdorff_measure_borel_regular R Y m.+1.
have hFin : (mu A< +oo)%E := le_lt_trans (measure_mono hm hAW) hW.2.
have hFinite : mu A \is a fin_num by rewrite (ge0_fin_numE (measure_nonnegative hm _)).
pose mass := fine (mu A).
have hMass : mu A=mass%:E := esym (fineK hFinite).
have hMassPos : 0<mass by move: hPos; rewrite -/mu hMass lte_fin.
pose e := mass/2.
have he : 0<e by rewrite /e divr_gt0 // ltr0n.
have heSmall : (e%:E<mu A)%E.
  by rewrite hMass lte_fin /e ltr_pdivrMr ?ltr0n // ltr_pMr // ltr1n.
have hClosed C (hc : closed C) : measure_measurable mu C.
  exact: (borel_regular_borel_measurable hm hReg (closed_borel_set hc)).
have [F [_ [hF hLoss]]] := measure_rectifiable_finite_approximation hClosed hW he.
have hBad : (mu (A `\` F)<mu A)%E.
  apply: (le_lt_trans _ (lt_trans hLoss heSmall)).
  apply: (@measure_mono R Y mu hm)=> x [hx hn]; by split; first exact: hAW x hx.
have hIntersection : (0<mu (A `&` F))%E.
  rewrite ltNge; apply/negP=> hLe.
  have hZero : mu (A `&` F)=0%E.
    apply/eqP; rewrite eq_le hLe (measure_nonnegative hm); reflexivity.
  have hCover : A `<=` (A `&` F) `|` (A `\` F).
    move=> x hx; case: (pselect (F x))=> hh; [left|right]; by split.
  have hb := measure_binary_cover hm hCover.
  change (is_true (mu A<=mu (A `&` F)+mu (A `\` F))%E) in hb.
  rewrite hZero add0e in hb.
  by have := lt_le_trans hBad hb; rewrite ltxx.
have [B [f [_ [hLip hImage]]]] := positive_rectifiable_global_parametrization hF.
exists f; split=> //.
apply: (lt_le_trans hIntersection _).
apply: (@measure_mono R Y mu hm)=> y [hy hFcy]; split=> //.
rewrite -hImage in hFcy; have [x hx heq] := hFcy; by exists x.
Qed.
