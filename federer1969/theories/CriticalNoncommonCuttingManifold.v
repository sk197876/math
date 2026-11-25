(** Federer (1969), 3.4.2(7), p. 314: a smaller admissible
    manifold covers a relative neighbourhood of each point of C minus B. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import Hom ModuleQuotient GrassmannSubspaces GrassmannAbbreviations
  EuclideanInnerProduct InnerNorm HilbertFormCompactness RealNormUP NormMetric
  EuclideanProjectionSpace CriticalManifoldFamilyUP CriticalManifoldClassLaws
  CriticalFlatPiecesUP CriticalCommonZeroClosed CriticalNoncommonDerivative
  CriticalScalarizedChart CriticalScalarCuttingChart.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [critical_noncommon_cutting_manifold]: the local
    dimension-reduction assertion in 3.4.2(7), p. 314. Failure of
    the common tangent-zero condition supplies f, z, and a detecting
    functional. Its scalar chart has the required nonzero derivative.
    Choose the cutting manifold inside the proved open complement
    of B in C. Its intersection with C is a neighbourhood of a
    relative to C and contains no point of B. *)
Theorem critical_noncommon_cutting_manifold (R:realType) m d
    (Z:G (R_n R m) d) gamma k (Y:lmodType R) (NY:Y->R) (hNY:is_real_norm NY)
    (S C:set (R_n R m)) (p:euclidean_projection_space R m gamma.+1) g a:
  (1<=k)%N ->(m-d<=gamma)%N ->
  is_critical_manifold_chart k (grassmann_val Z) S p g ->C `<=` S ->C a ->
  ~critical_common_tangent_zero_set hNY (grassmann_val Z) S C k a ->
  exists V:set (R_n R m),critical_manifold_family Z gamma k V /\V `<=` S /\
    V `&` C `<=` C `\` critical_common_tangent_zero_set hNY (grassmann_val Z) S C k /\
    exists N:set (R_n R m),
      @open (real_norm_metric_space
        (inner_norm_real_norm (@euclidean_inner_productP R m))) N /\
      N a /\C `&` N `<=` V.
Proof.
move=>hk hDimension hChart hCS hc hNotB.
have [O [hOpen hB]]:=@critical_common_zero_chart_closed_form R m gamma.+1 k Y NY hNY
  (grassmann_val Z) S C p g hk hChart hCS.
have haO:O a.
  case:(pselect (O a))=>[hYes|hNo];first exact:hYes.
  exfalso;apply:hNotB;rewrite hB;by split.
have [f [L [z [y [alpha hWitness]]]]]:=
  @critical_noncommon_derivative_witness R m k Y NY hNY (grassmann_val Z) S C a
    hk hCS hc hNotB.
have [hf [hz [hOuter [hInner [hy [hAlpha hPositive]]]]]]:=hWitness.
pose F:=fun w=>alpha (f (g w)).
have hF:=@critical_scalarized_chart_class R m gamma.+1 k Y NY hNY (grassmann_val Z)
  S p g f alpha hChart hf.1 hAlpha.
have hChart1:=critical_manifold_chart_lower_class hk hChart.
have [D [hD hValue]]:=@critical_scalarized_chart_direction R m gamma.+1 Y NY hNY
  (grassmann_val Z) S p g f alpha a z y L hChart1 (hCS a hc) hAlpha hOuter hInner.
have hNonzero:D (euclidean_projection_linear p z)!=0 by rewrite hValue gt_eqF.
have hZero c (hcc:C c):F (euclidean_projection_linear p c)=0.
  by rewrite /F (critical_chart_left_inverse hChart (hCS c hcc)) (hf.2 c hcc) linear0.
have [V [hV [hVS [hVO [N [hN [haN hCN]]]]]]]:=
  @critical_scalar_cutting_chart R m d Z gamma k S C O p g F D a z hk hDimension
    hChart hCS hc hz hOpen haO hF hD hNonzero hZero.
exists V;split;first exact:hV.
split;first exact:hVS.
split.
- move=>x [hxV hxC];split;first exact:hxC.
  move=>hxB;rewrite hB in hxB.
  exact:(hxB.2 (hVO x hxV)).
- exists N;by repeat split.
Qed.
