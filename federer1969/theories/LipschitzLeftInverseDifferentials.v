(** Federer (1969), 3.2.8, p. 247: for
    Lipschitz u,v on R^m, Dv(u(x)) composed
    with Du(x) is identity almost everywhere
    on C={x:v(u(x))=x}. Preserve the actual
    partial differential graphs and both existence claims. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology.
From Federer Require Import Hom TensorUP GrassmannAbbreviations EuclideanInnerProduct InnerNorm InnerMetric HilbertFormCompactness
  EuclideanLebesgueDimensions EuclideanLebesgueBoxes LipschitzUP NormMetricScaleContinuity ContinuousEqualizerClosed
  TopologicalBorel MeasureUP MeasureAlmostUP MeasureAlmostBasic PartialFunctionUP NormDifferentialUP NormDifferential
  Rademacher EuclideanFullDensityCore EuclideanLipschitzNullImages DensityLeftInverseDifferentials.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [lipschitz_left_inverse_differentiability_almost]:
    the common actual differentiability domain in
    the proof of Federer 3.2.8, p. 247.
    The inverse image of the second null set
    is controlled on C by its Lipschitz image
    under v; no global inverse or injectivity is assumed. *)
Lemma lipschitz_left_inverse_differentiability_almost (R:realType) m
    (u v:inner_metric_space (@euclidean_inner_productP R m)->
      inner_metric_space (@euclidean_inner_productP R m)):
  is_metric_lipschitz setT u -> is_metric_lipschitz setT v ->
  measure_almost_everywhere_on (@euclidean_lebesgue_measure R m)
    [set x|v (u x)=x]
    [set a| norm_differentiable_at (inner_norm (@euclidean_inner_productP R m))
        (inner_norm (@euclidean_inner_productP R m)) setT u a /\
      norm_differentiable_at (inner_norm (@euclidean_inner_productP R m))
        (inner_norm (@euclidean_inner_productP R m)) setT v (u a)].
Proof.
move=>hu hv.
pose X:=inner_metric_space (@euclidean_inner_productP R m).
pose N:=inner_norm (@euclidean_inner_productP R m).
pose mu:=@euclidean_lebesgue_measure R m; have hm:=euclidean_lebesgue_is_measure R m.
pose Pu:=fun a:X=>norm_differentiable_at N N setT u a.
pose Pv:=fun a:X=>norm_differentiable_at N N setT v a.
pose C:= [set x:X|v (u x)=x].
have hU:measure_almost_everywhere mu Pu:=federer_3_1_6 hu.
have hV:measure_almost_everywhere mu Pv:=federer_3_1_6 hv.
have hImage:mu (v @` (~` Pv))=0%E:=euclidean_lipschitz_selfmap_null_image hv hV.
have hPre:measure_almost_everywhere_on mu C [set x|Pv (u x)].
  apply:(measure_null_subset hm _ hImage)=>x [hx hn].
  exists (u x); first exact hn; exact hx.
apply:(measure_almost_everywhere_on_implication _ _ _).2.
apply:(@measure_almost_everywhere_mono R [the choiceType of X] mu hm _ _ _
  (measure_almost_everywhere_and hm hU
    ((measure_almost_everywhere_on_implication _ _ _).1 hPre)))=>x [hx hy] hC.
split; first exact hx; exact (hy hC).
Qed.

(** Source for [federer_3_2_8]: complete statement of
    Federer 3.2.8, p. 247. Both actual
    differentials exist and their composition is identity
    at almost every point where v composed with
    u is identity. The theorem includes m=0;
    the positive-dimensional proof uses the printed
    density and chain-rule argument. *)
Theorem federer_3_2_8 (R:realType) m
    (u v:inner_metric_space (@euclidean_inner_productP R m)->
      inner_metric_space (@euclidean_inner_productP R m)):
  is_metric_lipschitz setT u -> is_metric_lipschitz setT v ->
  measure_almost_everywhere_on (@euclidean_lebesgue_measure R m)
    [set x|v (u x)=x]
    [set a|exists L M:Hom (R_n R m) (R_n R m),
      partial_function_graph
        (norm_differential (inner_norm_real_norm (@euclidean_inner_productP R m))
          (inner_norm_real_norm (@euclidean_inner_productP R m)) setT u) a L /\
      partial_function_graph
        (norm_differential (inner_norm_real_norm (@euclidean_inner_productP R m))
          (inner_norm_real_norm (@euclidean_inner_productP R m)) setT v) (u a) M /\
      hom_comp M L=hom_of_linear (linear_id (R_n R m))].
Proof.
move=>hu hv.
pose X:=inner_metric_space (@euclidean_inner_productP R m).
pose N:=inner_norm (@euclidean_inner_productP R m).
pose hN:=inner_norm_real_norm (@euclidean_inner_productP R m).
pose mu:=@euclidean_lebesgue_measure R m; have hm:=euclidean_lebesgue_is_measure R m.
pose C:= [set x:X|v (u x)=x].
have hCu:continuous u.
  have [L [hL hb]]:=hu.
  exact (metric_fixed_lipschitz_continuous hb.1 (fun x y=>hb.2 x y Logic.I Logic.I)).
have hCv:continuous v.
  have [L [hL hb]]:=hv.
  exact (metric_fixed_lipschitz_continuous hb.1 (fun x y=>hb.2 x y Logic.I Logic.I)).
have hComp:continuous (fun x:X=>v (u x)).
  move=>x; exact (continuous_comp (hCu x) (hCv (u x))).
have hClosed:closed C.
  apply:(@continuous_equalizer_closed [the topologicalType of X] [the topologicalType of X]
    (fun x=>v (u x)) id); [exact:metric_hausdorff|exact hComp|by move=>x].
have hCMeas:measure_measurable mu C:=euclidean_borel_measurable (closed_borel_set hClosed).
have [S [hSC [hNull hDensity]]]:=euclidean_full_density_core_exists hCMeas.
have hDiff:=lipschitz_left_inverse_differentiability_almost hu hv.
have hCore:measure_almost_everywhere_on mu C S:=hNull.
apply:(measure_almost_everywhere_on_implication _ _ _).2.
apply:(@measure_almost_everywhere_mono R [the choiceType of X] mu hm _ _ _
  (measure_almost_everywhere_and hm
    ((measure_almost_everywhere_on_implication _ _ _).1 hDiff)
    ((measure_almost_everywhere_on_implication _ _ _).1 hCore)))=>a [hDa hSa] ha.
have [[L hL] [M hM]]:=hDa ha; have hS:S a:=hSa ha.
exists L,M; split; first exact ((norm_differential_graph (inner_norm_real_norm (@euclidean_inner_productP R m)) (inner_norm_real_norm (@euclidean_inner_productP R m)) setT u a L).2 hL).
split; first exact ((norm_differential_graph (inner_norm_real_norm (@euclidean_inner_productP R m)) (inner_norm_real_norm (@euclidean_inner_productP R m)) setT v (u a) M).2 hM).
apply:(density_left_inverse_differential_identity hS _ (hDensity a hS) hL hM).
move=>x hx; exact (hSC x hx).
Qed.
