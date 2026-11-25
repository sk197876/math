(** Federer (1969), 3.2.31, pp. 268–269: rectifiable
    fibre-threshold sets for a globally extended map restricted
    to its original finite measurable rectifiable source.
    Zero target degree and zero-dimensional target are retained. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals
  constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct InnerMetric
  LipschitzUP HausdorffMeasure HausdorffFibreCutoffs HausdorffCountableNull
  RectifiableSetUP RectifiablePositiveFibreLocus CountablyMeasureRectifiableOperations
  FiniteHausdorffZeroRectifiability FiniteFibreThreshold MeasureUP MeasureAlmostBasic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

Section RectifiableThreshold.
Variable R:realType.
Variables n v:nat.
Local Notation X:=(inner_metric_space (@euclidean_inner_productP R n)).
Local Notation Y:=(inner_metric_space (@euclidean_inner_productP R v)).

(** Source for [rectifiable_fibre_threshold_rectifiable]: the
    complete conclusion of Federer 3.2.31, pp. 268–269,
    expressed with an auxiliary global Lipschitz extension.
    The original W remains the source in every fibre. All
    natural dimensions, non-strict thresholds, zero Lipschitz
    bounds, and infinite individual fibre masses are included.
    Target-threshold measurability is also established. *)
Theorem rectifiable_fibre_threshold_rectifiable (F:X->Y) (W:set X) m mu L (lambda:R):
  (mu<=m)%N ->(0<lambda)%R ->
  is_measure_m_rectifiable (@hausdorff_measure R X m) m W ->
  measure_measurable (@hausdorff_measure R X m) W ->
  is_metric_lipschitz_bound setT F L ->
  measure_measurable (@hausdorff_measure R Y mu)
    [set y|lambda%:E<=hausdorff_fibre_mass F W (m-mu) y] /\
  is_measure_m_rectifiable (@hausdorff_measure R Y mu) mu
    [set y|lambda%:E<=hausdorff_fibre_mass F W (m-mu) y].
Proof.
move=>hMu hLambda hRect hMeas hLip.
pose Z:set Y:=[set y|lambda%:E<=hausdorff_fibre_mass F W (m-mu) y].
pose beta:=@hausdorff_measure R Y mu.
have hb:is_measure beta:=@hausdorff_measure_is_measure R Y mu.
have hSourceMeas:measure_measurable (@hausdorff_measure R X ((m-mu)+mu)) W.
  by rewrite (subnK hMu).
have hSourceFinite:@hausdorff_measure R X ((m-mu)+mu) W< +oo.
  rewrite (subnK hMu); exact hRect.2.
have [hZMeas hZFinite]:=@finite_fibre_threshold_measurable R n v F W L (m-mu) mu lambda
  hLambda hLip hSourceMeas hSourceFinite.
split; first exact hZMeas.
case:(eqVneq mu 0%N)=>hZero.
- rewrite hZero in hZFinite *; exact:finite_hausdorff_zero_rectifiable hZFinite.
have hmu:(0<mu)%N by rewrite lt0n.
case:(eqVneq v 0%N)=>hv.
- have hAllZero (y:Y):y=0%R.
    move:y; rewrite hv=>y; exact:coordinate_zero.
  have hNull:beta Z=0.
    apply:(measure_null_subset hb _ (@hausdorff_positive_degree_singleton_zero R Y mu (0%R:Y) hmu)).
    move=>y hy; exact:hAllZero.
  split; last exact hZFinite.
  exact (@countably_measure_rectifiable_null R Y beta mu Z hb hNull).
have hvPositive:(0<v)%N by rewrite lt0n.
have hmPositive:(0<m)%N:=leq_trans hmu hMu.
have hDim:(m.-1).+1=((m-mu)+mu)%N by rewrite (prednK hmPositive) (subnK hMu).
have hRect':is_measure_m_rectifiable (@hausdorff_measure R X (m.-1).+1) (m.-1).+1 W.
  by rewrite (prednK hmPositive).
have hMeas':measure_measurable (@hausdorff_measure R X (m.-1).+1) W.
  by rewrite (prednK hmPositive).
have hPositive:=@rectifiable_positive_fibre_locus_countably_rectifiable R m.-1 n v F W L (m-mu) mu
  hvPositive hmu hDim hRect' hMeas' hLip.
split; last exact hZFinite.
apply:(countably_measure_rectifiable_subset _ hPositive)=>y hy.
change (is_true (0<hausdorff_fibre_mass F W (m-mu) y)).
apply:lt_le_trans _ hy; by rewrite lte_fin.
Qed.
End RectifiableThreshold.
