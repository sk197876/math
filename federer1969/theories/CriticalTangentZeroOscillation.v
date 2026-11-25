(** Federer (1969), 3.4.2(7), p. 313: the class-one derivative
    oscillation tends to zero near a compact tangent-zero set. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets
  reals constructive_ereal topology lra.
From Federer Require Import Hom ModuleQuotient GrassmannAbbreviations EuclideanInnerProduct
  InnerNorm HilbertFormCompactness RealNormUP NormMetric NormDifferentialUP NormClassOneUP
  NormRegularity NormRegularityDerivativeField RelativeClassUP PartialFunctionUP
  RelativeDifferential ContinuousMultilinearUP ContinuousMultilinearNorm
  ContinuousMultilinearOne ContinuousMultilinearSealed EuclideanProjectionSpace
  ExtendedSupremumUP PositiveRightOrderLimit RadialRatioZero RealPower
  CriticalManifoldFamilyUP CriticalManifoldChartLaws CriticalFlatPiecesUP
  CriticalChartRetractionClass CriticalChartTangentZero CriticalRelativeDifferentialLaws
  CriticalCompactOperatorZero CriticalOscillationUP CriticalOscillation.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [critical_tangent_zero_zeta_limit]: the assertion
    ζ(S,B,f,0,delta)->0 in the class-one case of 3.4.2(7), p. 313.
    The same continuity estimate also supplies the class-one case
    of (9). Use the genuine derivative field of f composed with r,
    its public operator norm, and compact-base uniform continuity.
    The original relative derivative and punctured tests are retained. *)
Theorem critical_tangent_zero_zeta_limit (R:realType) m mu
    (Y:lmodType R) (NY:Y->R) (hNY:is_real_norm NY)
    (Z:subspace (R_n R m)) (S C:set (R_n R m))
    (p:euclidean_projection_space R m mu) g (f:R_n R m->Y):
  is_critical_manifold_chart 1 Z S p g ->
  C `<=` critical_tangent_zero_locus hNY Z S f ->
  @compact (real_norm_metric_space
    (inner_norm_real_norm (@euclidean_inner_productP R m))) C ->
  norm_class_relative (inner_norm_real_norm (@euclidean_inner_productP R m))
    hNY S S f 1 ->
  positive_right_extended_order_limit
    (fun delta=>critical_zeta hNY Z S C f 0 delta) 0%E.
Proof.
move=>hChart hCZero hC hf.
pose X:=R_n R m.
pose NX:=inner_norm (@euclidean_inner_productP R m).
pose hNX:=inner_norm_real_norm (@euclidean_inner_productP R m).
pose W:=@ContinuousMultilinear.space R 1 X Y NX NY hNX hNY.
pose ev:=@ContinuousMultilinear.evaluation R 1 X Y NX NY hNX hNY.
pose WN:=@ContinuousMultilinear.norm R 1 X Y NX NY hNX hNY.
pose hW:=@ContinuousMultilinear.laws R 1 X Y NX NY hNX hNY.
pose U:=fun x=>(euclidean_projection_linear p @` S) (euclidean_projection_linear p x).
pose r:=fun x=>g (euclidean_projection_linear p x).
pose F:=fun x=>f (r x).
have hR:=critical_chart_retraction_class hChart.
have [Dr hDr]:=(norm_class_firstP hNX hNX U r).1 hR.
have hF:=critical_chart_relative_composition_class hChart hf.
have [G [hG hDiff]]:=@norm_class_derivative_field R X Y NX NY hNX hNY U F 0 hF.
have hCS:C `<=` S by move=>c hc;exact:(hCZero c hc).1.
have hCU:C `<=` U by move=>c hc;exists c;first exact:(hCS c hc).
have hZero c z (hc:C c) (hz:Z z):continuous_multilinear_one_operator hW (G c) z=0.
  have hcU:U c:=hCU c hc.
  have h:=@critical_chart_tangent_zero_iff R m mu 1 Y NY hNY Z S p g f c
    (Dr c) (continuous_multilinear_one_operator hW (G c)) hChart (hCS c hc)
    (norm_class_one_differential hDr hcU) (hDiff c hcU).
  exact:((h.1 (hCZero c hc)) z hz).
apply:nonnegative_positive_right_limit_zero.
- move=>delta hdelta;exact:critical_zeta_nonnegative.
- move=>epsilon hEpsilon.
  have hHalf:0<epsilon/2 by rewrite divr_gt0 //.
  have [d [hd hNear]]:=@critical_compact_operator_zero_control R X Y W NX NY hNX hNY
    ev WN hW Z U C G hC hCU (norm_class_continuous hG) hZero (epsilon/2) hHalf.
  exists d;split;first exact:hd.
  move=>delta hDelta hSmallDelta.
  have hBound:(critical_zeta hNY Z S C f 0 delta<=(epsilon/2)%:E)%E.
    apply:(extended_supremum_least (critical_zeta_laws hNY Z S C f 0 delta)).
    move=>q [->|[x [c [z [L [y hData]]]]]].
    + by rewrite lee_fin;exact:ltW hHalf.
    + have [hx [hc [hZ [hDist [hz [hUnit [hOuter [hInner ->]]]]]]]]:=hData.
      rewrite real_power_zero_exponent divr1 lee_fin.
      have hxU:U x by exists x.
      have hAgree a (ha:S a) (haU:U a):f a=F a.
        by rewrite /F /r (critical_chart_left_inverse hChart ha).
      have [L0 [hOuter0 hValues]]:=@critical_relative_differential_from_extension
        R X Y NX NY hNX hNY U S F f x
        (continuous_multilinear_one_operator hW (G x)) hx hAgree (hDiff x hxU).
      have hSame:L=L0:=partial_function_single_valued hOuter hOuter0.
      have hActual:partial_function_graph L0 z y by rewrite -hSame.
      have hValue:continuous_multilinear_one_operator hW (G x) z=y:=((hValues z y).1 hActual).2.
      have hNearValue:=hNear x c hc hxU (le_lt_trans (andP hDist).2 hSmallDelta) z hz hUnit.
      rewrite hValue in hNearValue;exact:ltW hNearValue.
  apply:(le_lt_trans hBound).
  rewrite lte_fin;lra.
Qed.
