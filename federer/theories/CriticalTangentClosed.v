(** Federer (1969), 3.4.2(9), p. 316: the original
    tangent-critical set is relatively closed in the source manifold. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals topology.
From Federer Require Import Hom ModuleQuotient GrassmannAbbreviations EuclideanInnerProduct
  InnerNorm HilbertFormCompactness RealNormUP NormMetric NormClassOneUP NormRegularity
  RelativeClassUP EuclideanProjectionSpace CriticalManifoldFamilyUP CriticalFlatPiecesUP
  CriticalChartRetractionClass CriticalChartTangentZero CriticalChartDerivativeLoci
  CriticalManifoldCompactCover.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [critical_tangent_zero_relatively_closed]: the
    closed set C used before applying (7) in the proof of
    3.4.2(9), p. 316. The genuine ambient derivative of
    f composed with the actual retraction annihilates Z precisely
    on the original relative tangent-zero locus. Its nonzero
    locus is open, proving the required relative closedness. *)
Theorem critical_tangent_zero_relatively_closed (R:realType) m mu
    (Y:lmodType R) (NY:Y->R) (hNY:is_real_norm NY)
    (Z:subspace (R_n R m)) (S:set (R_n R m))
    (p:euclidean_projection_space R m mu) g (f:R_n R m->Y):
  is_critical_manifold_chart 1 Z S p g ->
  norm_class_relative (inner_norm_real_norm (@euclidean_inner_productP R m)) hNY S S f 1 ->
  @is_relatively_closed_source (real_norm_metric_space
    (inner_norm_real_norm (@euclidean_inner_productP R m))) S
    (critical_tangent_zero_locus hNY Z S f).
Proof.
move=>hChart hf.
pose X:=R_n R m.
pose NX:=inner_norm (@euclidean_inner_productP R m).
pose hNX:=inner_norm_real_norm (@euclidean_inner_productP R m).
pose U:=fun x=>(euclidean_projection_linear p @` S) (euclidean_projection_linear p x).
pose r:=fun x=>g (euclidean_projection_linear p x).
pose F:=fun x=>f (r x).
pose O:=critical_chart_derivative_nonzero_locus NY Z S p g f.
have hOpen:@open (real_norm_metric_space hNX) O:=
  @critical_chart_derivative_nonzero_open R m mu Y NY hNY Z S p g f hChart hf.
have hR:=critical_chart_retraction_class hChart.
have [Dr hDr]:=(norm_class_firstP hNX hNX U r).1 hR.
have hF:=critical_chart_relative_composition_class hChart hf.
have [DF hDF]:=(norm_class_firstP hNX hNY U F).1 hF.
exists (~` O);split;first exact:open_closedC hOpen.
apply/seteqP;split.
- move=>x hx;split;first exact:hx.1.
  move=>[hxU [D [hD [z [hz hNonzero]]]]].
  have hIff:=@critical_chart_tangent_zero_iff R m mu 1 Y NY hNY Z S p g f x
    (Dr x) D hChart hx.1 (norm_class_one_differential hDr hxU) hD.
  have hZero:=(hIff.1 hx) z hz.
  by rewrite hZero eqxx in hNonzero.
- move=>x [hxS hNoO].
  have hxU:U x by exists x.
  have hActual:=norm_class_one_differential hDF hxU.
  apply:(@critical_chart_tangent_zero_iff R m mu 1 Y NY hNY Z S p g f x
    (Dr x) (DF x) hChart hxS (norm_class_one_differential hDr hxU) hActual).2.
  move=>z hz;case:(eqVneq (DF x z) 0)=>[hZero|hNonzero];first exact:hZero.
  exfalso;apply:hNoO;split;first exact:hxU.
  exists (DF x);split;first exact:hActual.
  by exists z.
Qed.
