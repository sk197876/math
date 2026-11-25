(** Federer (1969), 3.2.16 and 3.2.20, pp. 252–256:
    restricting a measure to W contained in O forces its
    approximate tangent into the ordinary tangent of O.
    This transfers actual tangent exterior bounds to the
    approximate Jacobian, supporting 3.2.47(3), p. 283. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology.
From Federer Require Import Hom GrassmannAbbreviations EuclideanInnerProduct InnerNorm HilbertFormCompactness
  NormDifferentialUP NormMetric TangentConeUP PartialFunctionUP PartialFunctionBasic PartialFunctionSourceRestriction
  MeasureUP MeasureBasic MeasureRestriction MetricDensityZeroPowerMass MeasureApproximateTangentUP
  MeasureApproximateTangentBasic MeasureApproximateDifferentialUP MeasureApproximateDifferentialUniqueness
  AmbientApproximateDifferentialRestriction MeasureApproximateJacobianUP MeasureApproximateJacobian
  PartialExteriorNormUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [restricted_approximate_jacobian_tangent_bound]:
    the actual partial exterior norm on the approximate
    tangent is bounded by an ordinary containing-tangent bound,
    by 3.2.16–3.2.20, pp. 252–256. Supporting
    3.2.47(3), p. 283; no tangent-plane,
    source-measurability or source-finiteness premise is added. *)
Theorem restricted_approximate_jacobian_tangent_bound (R:realType) n k m q
    (phi:set (R_n R n)->\bar R) (W O:set (R_n R n))
    (F:R_n R n->R_n R k) a (D:Hom (R_n R n) (R_n R k)) J L:
  is_measure phi ->W `<=` O ->
  has_norm_differential (inner_norm (@euclidean_inner_productP R n))
    (inner_norm (@euclidean_inner_productP R k)) setT F a D ->
  (0<=L)%R ->
  is_partial_exterior_bound q (partial_function_source_restrict
    (norm_tangent_cone (inner_norm (@euclidean_inner_productP R n)) O a)
    (partial_function_total D)) L ->
  partial_function_graph (measure_approximate_jacobian (measure_restrict phi W) m q
    (partial_function_source_restrict W (partial_function_total F))) a J ->J<=L.
Proof.
move=>hPhi hWO hD hL hBound hJ.
pose X:=R_n R n.
pose hX:=inner_norm_real_norm (@euclidean_inner_productP R n).
pose hY:=inner_norm_real_norm (@euclidean_inner_productP R k).
pose nu:=measure_restrict phi W.
have hNu:is_measure nu:=measure_restrict_is_measure hPhi W.
have hOutside:nu (~` O)=0%E.
  rewrite /nu /measure_restrict.
  have hEmpty:W `&` ~` O=set0.
    apply/seteqP; split=>[x [hx hn]|x []]; exfalso; exact (hn (hWO x hx)).
  rewrite hEmpty; exact (measure_empty hPhi).
have hZero:=@null_set_metric_density_zero R (real_norm_metric_space hX) m nu (~` O) a hNu hOutside.
have hContain:=@measure_approximate_tangent_ordinary R X _ hX nu m a O hZero.
have [d [hApprox hNorm]]:=(measure_approximate_jacobian_graph _ _ _ _ _ _).1 hJ.
have hActual:=@ambient_differential_restricted_approximate_graph R X (R_n R k) _ _ hX hY
  phi m W F a D hPhi hD.
have hSame:d=partial_function_source_restrict
    (measure_approximate_tangent_cone hX nu m a) (partial_function_total D).
  exact (measure_approximate_differential_unique hApprox hActual).
rewrite hSame in hNorm.
apply:(partial_exterior_norm_least hNorm hL).
move=>v w hGraph hUnit; apply:(hBound v w _ hUnit)=>i.
have [hTan hValue]:=hGraph i.
exact (conj (hContain _ hTan) hValue).
Qed.
