(** Federer (1969), 3.2.28, pp. 265–267:
    the area and coarea Jacobians on these smooth manifolds
    use their actual geometric tangents. The approximate
    tangent is contained in that tangent and has the same
    dimension almost everywhere, by 3.2.19, p. 256. *)
From mathcomp Require Import all_boot all_order all_algebra reals classical_sets constructive_ereal topology.
From Federer Require Import ModuleQuotient GrassmannSubspaces GrassmannDimensionInclusion
  GrassmannAbbreviations EuclideanInnerProduct InnerNorm InnerMetric HilbertFormCompactness
  NormMetric TangentConeUP EuclideanSubmanifoldUP SubmanifoldTangentPlane
  MeasureUP MeasureBasic MeasureRestriction MeasureAlmostUP MeasureAlmostBasic
  PartialFunctionUP MetricDensities MetricDensityZeroPowerMass
  MeasureApproximateTangentUP MeasureApproximateTangentBasic RectifiableSetUP
  RectifiableTangentPlaneUP RectifiableDensityTangent HausdorffMeasure.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [submanifold_subset_approximate_tangent_almost]: the
    identification underlying the Jacobian calculations in
    Federer 3.2.28, pp. 265–267, by 3.1.21,
    p. 234, and 3.2.19, p. 256. The source
    is a measurable finite-mass rectifiable subset of the manifold;
    no equality at exceptional points is asserted. *)
Theorem submanifold_subset_approximate_tangent_almost (R:realType) n mu k
    (B K:set (R_n R n)):
  (1<=k)%N ->@is_euclidean_submanifold R n mu k B ->K `<=` B ->
  is_measure_m_rectifiable (@hausdorff_measure R
    (inner_metric_space (@euclidean_inner_productP R n)) mu) mu K ->
  measure_measurable (@hausdorff_measure R
    (inner_metric_space (@euclidean_inner_productP R n)) mu) K ->
  let H:=@hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R n)) mu in
  measure_almost_everywhere_on H K [set a|
    measure_approximate_tangent_cone (inner_norm_real_norm (@euclidean_inner_productP R n))
      (measure_restrict H K) mu a=
    norm_tangent_cone (inner_norm (@euclidean_inner_productP R n)) B a].
Proof.
move=>hk hB hKB hRect hMeas H.
pose X:=R_n R n.
pose NX:=inner_norm (@euclidean_inner_productP R n).
pose hNX:=inner_norm_real_norm (@euclidean_inner_productP R n).
pose nu:=measure_restrict H K.
have hH:=@hausdorff_measure_is_measure R (inner_metric_space (@euclidean_inner_productP R n)) mu.
have hnu:is_measure nu:=measure_restrict_is_measure hH K.
have hFull:nu (~` B)=0%E.
  rewrite /nu /measure_restrict.
  have hEmpty:K `&` (~` B)=set0.
    apply/seteqP; split=>[x [hx hn]|x []]; exfalso; exact:hn (hKB x hx).
  rewrite hEmpty; exact:measure_empty hH.
have hPlanes:=(federer_3_2_19 hRect hMeas).1.
apply:(measure_null_subset hH _ hPlanes)=>a [ha hn].
split; first exact ha.
move=>[_ [P hP]]; apply:hn.
have [Q hQ]:=@submanifold_tangent_plane R n mu k B a hk hB (hKB a ha).
have hDensity:=@null_set_metric_density_zero R (real_norm_metric_space hNX) mu nu (~` B) a hnu hFull.
have hSub:=@measure_approximate_tangent_ordinary R X NX hNX nu mu a B hDensity.
have hPQ v:grassmann_val P v ->grassmann_val Q v.
  move=>hv; rewrite -hQ; apply:hSub.
  by rewrite hP.
change (measure_approximate_tangent_cone hNX nu mu a=norm_tangent_cone NX B a).
have hPE:measure_approximate_tangent_cone hNX nu mu a=[set v|grassmann_val P v]:=hP.
have hQE:norm_tangent_cone NX B a=[set v|grassmann_val Q v]:=hQ.
rewrite hPE hQE; apply/seteqP; split=>v hv.
- exact:hPQ v hv.
- exact:(grassmann_equal_dimension_inclusion hPQ v).2 hv.
Qed.
