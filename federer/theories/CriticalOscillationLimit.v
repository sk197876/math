(** Federer (1969), 3.4.2(6), pp. 311–312: derivative oscillation
    of order lambda-1 gives function oscillation of order lambda. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets
  reals constructive_ereal topology.
From Federer Require Import ModuleQuotient GrassmannSubspaces GrassmannAbbreviations
  EuclideanInnerProduct InnerNorm HilbertFormCompactness NormMetric RealNormUP
  NormClassOneUP NormRegularity RelativeClassUP EuclideanProjectionSpace
  CriticalManifoldFamilyUP CriticalChartRetractionClass CriticalTubeLipschitz
  CriticalEtaZetaComparison CriticalOscillation CriticalDiscreteOscillation
  PositiveRightOrderLimit StructureZeroLimitComparison RealPower.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [critical_chart_oscillation_zero_limit]: the
    positive-dimensional chart proof of 3.4.2(6), p. 312. Compactness
    gives one tube and one finite Lipschitz constant. The scaled
    comparison then transfers the ordinary positive-cutoff limit.
    No completeness or finite dimension of the target is required. *)
Theorem critical_chart_oscillation_zero_limit (R:realType) m mu
    (Y:lmodType R) (NY:Y->R) (hNY:is_real_norm NY)
    (Z:subspace (R_n R m)) (S C:set (R_n R m))
    (p:euclidean_projection_space R m mu) g (f:R_n R m->Y) lambda:
  is_critical_manifold_chart 1 Z S p g ->C `<=` S ->
  @compact (real_norm_metric_space
    (inner_norm_real_norm (@euclidean_inner_productP R m))) C ->
  norm_class_relative (inner_norm_real_norm (@euclidean_inner_productP R m))
    hNY S S f 1 ->1<=lambda ->
  positive_right_extended_order_limit
    (fun delta=>critical_zeta hNY Z S C f (lambda-1) delta) 0%E ->
  positive_right_extended_order_limit
    (fun delta=>critical_eta NY Z S C f lambda delta) 0%E.
Proof.
move=>hChart hCS hC hf hLambda hLimit.
pose X:=R_n R m.
pose NX:=inner_norm (@euclidean_inner_productP R m).
pose hNX:=inner_norm_real_norm (@euclidean_inner_productP R m).
pose U:=fun x=>(euclidean_projection_linear p @` S) (euclidean_projection_linear p x).
pose r:=fun x=>g (euclidean_projection_linear p x).
have hR:norm_class_one NX NX U r.
  exact:(norm_class_firstP hNX hNX U r).1 (critical_chart_retraction_class hChart).
have hF:norm_class_one NX NY U (fun x=>f (r x)).
  exact:(norm_class_firstP hNX hNY U (fun x=>f (r x))).1
    (critical_chart_relative_composition_class hChart hf).
have hCU:C `<=` U by move=>c hc;exists c;first exact:(hCS c hc).
have [e [T [M [he [hM [hTube [hCompact [hTU hLip]]]]]]]]:=
  @critical_compact_tube_lipschitz_bound R m C U r hC hCU hR.
have hMpositive:0<M:=lt_le_trans ltr01 hM.
have hPower:0<real_power M lambda:=@real_power_strictly_positive R M lambda hMpositive.
apply:(@structure_zero_limit_scaled_comparison R
  (fun delta=>critical_eta NY Z S C f lambda delta)
  (fun delta=>critical_zeta hNY Z S C f (lambda-1) delta)
  M (real_power M lambda) e hMpositive hPower he).
- move=>delta hdelta;exact:critical_eta_nonnegative.
- move=>delta hdelta.
  exact:(@critical_chart_eta_zeta_comparison R m mu 1 Y NY hNY Z S C T p g f
    e M lambda delta hChart hTube hCS hTU hM hLip hR hF hLambda hdelta).
- exact:hLimit.
Qed.

(** Source for [critical_oscillation_zero_limit]: the complete
    assertion (6) of 3.4.2, p. 311, proved on p. 312. Retain the
    original compact subset, relative class-one function, arbitrary
    normed target, lambda>=1, and ordinary positive-cutoff limits.
    The discrete case follows from compact isolation; the remaining
    cases use the projection chart required by Ω(mu,1). *)
Theorem critical_oscillation_zero_limit (R:realType) m d
    (Z:G (R_n R m) d) mu (Y:lmodType R) (NY:Y->R) (hNY:is_real_norm NY)
    (S C:set (R_n R m)) (f:R_n R m->Y) lambda:
  critical_manifold_family Z mu 1 S ->C `<=` S ->
  @compact (real_norm_metric_space
    (inner_norm_real_norm (@euclidean_inner_productP R m))) C ->
  norm_class_relative (inner_norm_real_norm (@euclidean_inner_productP R m))
    hNY S S f 1 ->1<=lambda ->
  positive_right_extended_order_limit
    (fun delta=>critical_zeta hNY (grassmann_val Z) S C f (lambda-1) delta) 0%E ->
  positive_right_extended_order_limit
    (fun delta=>critical_eta NY (grassmann_val Z) S C f lambda delta) 0%E.
Proof.
move=>[_ [_ [hS hAlternative]]] hCS hC hf hLambda hLimit.
case:hAlternative=>[hZero|[p [g hChart]]].
- subst mu;exact:(critical_zero_manifold_eta_zero_limit NY (grassmann_val Z) f lambda hS hCS hC).
- exact:(@critical_chart_oscillation_zero_limit R m mu Y NY hNY (grassmann_val Z)
    S C p g f lambda hChart hCS hC hf hLambda hLimit).
Qed.
