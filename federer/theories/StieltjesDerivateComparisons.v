(** Federer (1969), 2.9.19, p. 164: compare the finite induced-measure
    derivates with g' and s'. The proof uses short intervals with continuity
    endpoints, actual finite masses, and the already proved derivative and
    derivate estimates. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology lra.
From Federer Require Import RealMetricBackground CurveArcLength StieltjesImageMeasures
  FiniteStieltjesIntervalMasses RealBVContinuityPoints DenseRealOrderPoints
  ScalarIntervalDerivationContext ScalarIntervalDerivateBounds RealCurveDerivativeUP
  RealDerivativeIncrementBounds MeasureDerivates PartialFunctionUP LebesgueScalarMeasure.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory numFieldTopology.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [stieltjes_derivate_comparisons_at_continuity_point]: direct
    equalities/inequalities preceding the variation argument in Federer
    2.9.19, p. 164 If the finite derivative values are g'=v, s'=w, D(psi+)=p
    and D(psi-)=m, then p-m=v and p+m<=w. Continuity at x is an intermediate
    pointwise premise removed almost everywhere using countability of
    discontinuities. Nearby continuity endpoints supply finite interval
    masses; their difference equals the g-increment and their sum is bounded
    by the s-increment. *)
Lemma stieltjes_derivate_comparisons_at_continuity_point (R : realType)
    (g : R -> R) (psip psim : set R -> \bar R) (x v w p m : R) :
  curve_locally_finite_variation (g : R -> real_line_metric R) ->
  is_induced_measure_pair g psip psim -> g @ x --> g x ->
  has_real_curve_derivative g x v ->
  has_real_curve_derivative (arc_length (g : R -> real_line_metric R)) x w ->
  partial_function_graph (@measure_derivate R [the metricType R of real_line_metric R]
    psip (@lebesgue_scalar_measure R) (@scalar_nondegenerate_interval_relation R)) x p%:E ->
  partial_function_graph (@measure_derivate R [the metricType R of real_line_metric R]
    psim (@lebesgue_scalar_measure R) (@scalar_nondegenerate_interval_relation R)) x m%:E ->
  p-m=v /\ p+m<=w.
Proof.
move=> hg hpair hcx hG hS hP hM.
pose D : set (real_line_metric R) := [set t | g @ t --> g t].
have hDense : dense D := @real_bv_continuity_points_dense R g hg.
have hNear : forall e : R, 0<e ->
    p-m<=v+3*e /\ v<=p-m+3*e /\ p+m<=w+3*e.
  move=> e he.
  have [dp [hdp hPB]] := @scalar_interval_derivate_mass_bounds R psip x p e hP he.
  have [dm [hdm hMB]] := @scalar_interval_derivate_mass_bounds R psim x m e hM he.
  have [dg [hdg hGB]] := @real_derivative_interval_bounds R g x v e hG he.
  have [ds [hds hSB]] := @real_derivative_interval_bounds R
    (arc_length (g : R -> real_line_metric R)) x w e hS he.
  pose d := Num.min (Num.min dp dm) (Num.min dg ds).
  have hd : 0<d by rewrite /d !lt_min hdp hdm hdg hds.
  have hdL : d<=Num.min dp dm by rewrite /d ge_min lexx.
  have hdR : d<=Num.min dg ds by rewrite /d ge_min lexx orbT.
  have hLP : Num.min dp dm<=dp by rewrite ge_min lexx.
  have hLM : Num.min dp dm<=dm by rewrite ge_min lexx orbT.
  have hRG : Num.min dg ds<=dg by rewrite ge_min lexx.
  have hRS : Num.min dg ds<=ds by rewrite ge_min lexx orbT.
  have hdP : d<=dp := le_trans hdL hLP.
  have hdM : d<=dm := le_trans hdL hLM.
  have hdG : d<=dg := le_trans hdR hRG.
  have hdS : d<=ds := le_trans hdR hRS.
  have hxd : x<x+d by rewrite ltrDl.
  have [b [/andP [hxb hbUpper] hbD]] := @dense_real_open_interval_point R D x (x+d) hDense hxd.
  have hpos : 0<b-x by rewrite subr_gt0.
  have hwidth : b-x<d by lra.
  have hInt : x<=x<=b by apply/andP; split; first exact: lexx; exact: ltW hxb.
  have hwP : 0<b-x<dp by apply/andP; split=> //; exact: lt_le_trans hwidth hdP.
  have hwM : 0<b-x<dm by apply/andP; split=> //; exact: lt_le_trans hwidth hdM.
  have hwG : 0<b-x<dg by apply/andP; split=> //; exact: lt_le_trans hwidth hdG.
  have hwS : 0<b-x<ds by apply/andP; split=> //; exact: lt_le_trans hwidth hdS.
  have [P [M [hPE [hME [hP0 [hM0 [hInc hSum]]]]]]] :=
    @stieltjes_finite_interval_masses R g psip psim x b hg hpair hxb hcx hbD.
  have [hPL hPU] := hPB x b hInt hwP.
  have [hML hMU] := hMB x b hInt hwM.
  rewrite hPE !lee_fin in hPL hPU; rewrite hME !lee_fin in hML hMU.
  have [hGL hGU] := hGB x b hInt hwG.
  rewrite hInc in hGL hGU.
  have hSU := le_trans hSum (hSB x b hInt hwS).2.
  have hPLq : p-e<=P/(b-x) by rewrite ler_pdivlMr.
  have hPUq : P/(b-x)<=p+e by rewrite ler_pdivrMr.
  have hMLq : m-e<=M/(b-x) by rewrite ler_pdivlMr.
  have hMUq : M/(b-x)<=m+e by rewrite ler_pdivrMr.
  have hGLq : v-e<=(P-M)/(b-x) by rewrite ler_pdivlMr.
  have hGUq : (P-M)/(b-x)<=v+e by rewrite ler_pdivrMr.
  have hSUq : (P+M)/(b-x)<=w+e by rewrite ler_pdivrMr.
  rewrite mulrBl in hGLq hGUq; rewrite mulrDl in hSUq.
  split; first by lra.
  split; lra.
have hpmv : p-m<=v.
  apply/ler_addgt0Pr=> e he.
  have he4 : 0<e/4 by rewrite divr_gt0 // ltr0n.
  have [ha _] := hNear (e/4) he4; lra.
have hvpm : v<=p-m.
  apply/ler_addgt0Pr=> e he.
  have he4 : 0<e/4 by rewrite divr_gt0 // ltr0n.
  have [_ [ha _]] := hNear (e/4) he4; lra.
split; first by apply/le_anti/andP; split.
apply/ler_addgt0Pr=> e he.
have he4 : 0<e/4 by rewrite divr_gt0 // ltr0n.
have [_ [_ ha]] := hNear (e/4) he4; lra.
Qed.
