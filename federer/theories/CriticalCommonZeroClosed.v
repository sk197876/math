(** Federer (1969), 3.4.2(7), p. 312: the common tangent-zero
    set B is relatively closed and is compact when C is compact. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals topology.
From Federer Require Import Hom ModuleQuotient GrassmannAbbreviations EuclideanInnerProduct
  InnerNorm HilbertFormCompactness NormMetric RealNormUP NormClassOneUP NormRegularity
  EuclideanProjectionSpace CriticalManifoldFamilyUP CriticalManifoldClassLaws
  CriticalFlatPiecesUP CriticalChartRetractionClass CriticalChartTangentZero
  CriticalChartDerivativeLoci CriticalRelativeClassLaws CriticalManifoldCompactCover.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [critical_common_zero_chart_closed_form]: the
    closedness of B in the proof of 3.4.2(7), p. 312. Its complement
    in C is the union of the open nonzero derivative loci for all
    functions in Φ. Each field representative stays local to its
    proof; no countable family of functions is assumed. *)
Theorem critical_common_zero_chart_closed_form (R:realType) m mu k
    (Y:lmodType R) (NY:Y->R) (hNY:is_real_norm NY)
    (Z:subspace (R_n R m)) (S C:set (R_n R m))
    (p:euclidean_projection_space R m mu) g:
  (1<=k)%N ->is_critical_manifold_chart k Z S p g ->C `<=` S ->
  exists O:set (R_n R m),
    @open (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R m))) O /\
    critical_common_tangent_zero_set hNY Z S C k=C `&` ~` O.
Proof.
move=>hk hChartK hCS.
pose X:=R_n R m.
pose NX:=inner_norm (@euclidean_inner_productP R m).
pose hNX:=inner_norm_real_norm (@euclidean_inner_productP R m).
pose U:=fun x=>(euclidean_projection_linear p @` S) (euclidean_projection_linear p x).
pose r:=fun x=>g (euclidean_projection_linear p x).
have hChart:=critical_manifold_chart_lower_class hk hChartK.
have hR:=critical_chart_retraction_class hChart.
have [Dr hDr]:=(norm_class_firstP hNX hNX U r).1 hR.
pose Phi:set (X->Y):=[set f|critical_flat_function_class hNY S C f k].
pose O:=\bigcup_(f in Phi) critical_chart_derivative_nonzero_locus NY Z S p g f.
have hOpen:@open (real_norm_metric_space hNX) O.
  apply:bigcup_open=>f hf.
  exact:(@critical_chart_derivative_nonzero_open R m mu Y NY hNY Z S p g f hChart
    (critical_relative_class_lower hk hf.1)).
exists O;split;first exact:hOpen.
apply/seteqP;split.
- move=>x [hc hAll];split;first exact:hc.
  move=>[f hf [hxU [D [hD [z [hz hn]]]]]].
  have hIff:=@critical_chart_tangent_zero_iff R m mu 1 Y NY hNY Z S p g f x
    (Dr x) D hChart (hCS x hc) (norm_class_one_differential hDr hxU) hD.
  have hVanishing:forall z,Z z ->D z=0:=hIff.1 (hAll f hf).
  by rewrite (hVanishing z hz) eqxx in hn.
- move=>x [hc hNoO];split;first exact:hc.
  move=>f hf.
  have hxU:U x by exists x;first exact:(hCS x hc).
  pose F:=fun a=>f (r a).
  have hF:=critical_chart_relative_composition_class hChart
    (critical_relative_class_lower hk hf.1).
  have [D hD]:=(norm_class_firstP hNX hNY U F).1 hF.
  have hActual:=norm_class_one_differential hD hxU.
  apply:(@critical_chart_tangent_zero_iff R m mu 1 Y NY hNY Z S p g f x
    (Dr x) (D x) hChart (hCS x hc) (norm_class_one_differential hDr hxU) hActual).2.
  move=>z hz;case:(eqVneq (D x z) 0)=>[hZero|hNonzero];first exact:hZero.
  exfalso;apply:hNoO;exists f;first exact:hf.
  split;first exact:hxU.
  exists (D x);split;first exact:hActual.
  by exists z.
Qed.

(** Source for [critical_common_zero_chart_compact]: the compact
    set B used after the compact reduction in 3.4.2(7), p. 312.
    It is the intersection of compact C with the complement of the
    proved open union of nonzero derivative loci. *)
Theorem critical_common_zero_chart_compact (R:realType) m mu k
    (Y:lmodType R) (NY:Y->R) (hNY:is_real_norm NY)
    (Z:subspace (R_n R m)) (S C:set (R_n R m))
    (p:euclidean_projection_space R m mu) g:
  (1<=k)%N ->is_critical_manifold_chart k Z S p g ->C `<=` S ->
  @compact (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R m))) C ->
  @compact (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R m)))
    (critical_common_tangent_zero_set hNY Z S C k).
Proof.
move=>hk hChart hCS hC.
have [O [hOpen ->]]:=@critical_common_zero_chart_closed_form R m mu k Y NY hNY Z S C p g
  hk hChart hCS.
exact:(compact_closedI hC (open_closedC hOpen)).
Qed.

(** Source for [critical_common_zero_chart_relatively_closed]: the
    same common set B is relatively closed in S, as required by
    the class induction in 3.4.2(7), p. 313. Intersect the ambient
    closed representative of C with the closed vanishing locus. *)
Theorem critical_common_zero_chart_relatively_closed (R:realType) m mu k
    (Y:lmodType R) (NY:Y->R) (hNY:is_real_norm NY)
    (Z:subspace (R_n R m)) (S C:set (R_n R m))
    (p:euclidean_projection_space R m mu) g:
  (1<=k)%N ->is_critical_manifold_chart k Z S p g ->
  @is_relatively_closed_source (real_norm_metric_space
    (inner_norm_real_norm (@euclidean_inner_productP R m))) S C ->
  @is_relatively_closed_source (real_norm_metric_space
    (inner_norm_real_norm (@euclidean_inner_productP R m))) S
    (critical_common_tangent_zero_set hNY Z S C k).
Proof.
move=>hk hChart [F [hClosed hC]].
have hCS:C `<=` S by move=>x;rewrite hC;case.
have [O [hOpen hB]]:=@critical_common_zero_chart_closed_form R m mu k Y NY hNY Z S C p g
  hk hChart hCS.
exists (F `&` ~` O);split;first exact:(closedI hClosed (open_closedC hOpen)).
by rewrite hB hC setIA.
Qed.
