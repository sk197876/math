(** Federer (1969), 3.2.19, p. 256: extend the actual
    Lipschitz map on W globally by 2.10.43, p. 201.
    The extension is specified by its global bound and exact original
    partial graph, with no values silently assigned to the source map. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric
  PartialFunctionUP PartialFunctionBasic PartialFunctionSourceRestriction PartialFunctionExtensionality
  PartialFunctionExtensionUP PartialFunctionExtensionSealed PartialMetricLipschitz
  LipschitzUP KirszbraunExtensionUP KirszbraunExtension.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [euclidean_partial_lipschitz_global_extension]: supporting
    first extension in the proof of Federer 3.2.19, p. 256.
    Preserve exactly the supplied finite Lipschitz bound and actual graph.
    Existence uses only the earlier opaque total-extension and Kirszbraun
    laws; no new global selected witness or construction import is added. *)
Theorem euclidean_partial_lipschitz_global_extension (R : realType) n k
    (f : partial_function (R_n R n) (R_n R k)) (L : R) :
  @is_partial_metric_lipschitz_bound R
    (inner_metric_space (@euclidean_inner_productP R n))
    (inner_metric_space (@euclidean_inner_productP R k)) f L ->
  exists F : R_n R n -> R_n R k,
    @is_metric_lipschitz_bound R
      (inner_metric_space (@euclidean_inner_productP R n))
      (inner_metric_space (@euclidean_inner_productP R k)) setT F L /\
    f=partial_function_source_restrict (partial_function_domain f) (partial_function_total F).
Proof.
move=> hBound.
pose W := partial_function_domain f.
pose f0 := @PartialFunctionExtension.value (R_n R n) (R_n R k) f 0.
have h0 := @PartialFunctionExtension.laws (R_n R n) (R_n R k) f 0.
have hLocal : @is_metric_lipschitz_bound R
    (inner_metric_space (@euclidean_inner_productP R n))
    (inner_metric_space (@euclidean_inner_productP R k)) W f0 L.
  split; first exact hBound.1.
  move=> x y [a hxa] [b hyb].
  rewrite /f0 (h0 x a hxa) (h0 y b hyb); exact: hBound.2 x y a b hxa hyb.
pose F := @euclidean_lipschitz_extension R n k W f0 L hLocal.
have hF := @euclidean_lipschitz_extension_specification R n k W f0 L hLocal.
exists F; split; first exact: kirszbraun_extension_bound_law hF.
apply: partial_function_graph_extensionality=> x y; split.
- move=> hxy; have hx : W x by exists y.
  split; first exact hx.
  change (F x=y).
  rewrite (@kirszbraun_extension_agreement_law R n k W f0 F L hF x hx).
  exact: h0 x y hxy.
- move=> [hx hFy]; change (F x=y) in hFy.
  have [z hz] := hx.
  have hFz : F x=z.
    rewrite (@kirszbraun_extension_agreement_law R n k W f0 F L hF x hx).
    exact: h0 x z hz.
  have hzy : z=y := eq_trans (esym hFz) hFy.
  by rewrite -hzy.
Qed.
