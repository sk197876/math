(** Federer (1969), 3.2.22, p. 258: extend
    the inverse of each compact target chart with
    the same Lipschitz bound by 2.10.43, p. 201. *)
From mathcomp Require Import all_boot all_order all_algebra reals classical_sets topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric LipschitzUP
  RectifiableCompactChartsUP RectifiableCompactChartLaws MetricBiLipschitzInverse
  KirszbraunExtensionUP KirszbraunExtension.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [uniform_compact_chart_inverse_global_extension]:
    the Lipschitz map G_j with G_j on gamma_j(C_j)
    equal to the actual inverse and Lip(G_j)<=lambda,
    Federer 3.2.22, p. 258. The two chart
    distance laws prove the inverse bound; the existing
    opaque Kirszbraun laws give its global extension.
    This is an existence theorem, not a new selected map. *)
Lemma uniform_compact_chart_inverse_global_extension (R:realType) mu n
    (lambda:R) (C:set (R_n R mu)) (gamma:R_n R mu->R_n R n):
  is_uniform_compact_rectifiable_chart lambda C gamma ->
  exists G:R_n R n->R_n R mu,
    @is_metric_lipschitz_bound R (inner_metric_space (@euclidean_inner_productP R n))
      (inner_metric_space (@euclidean_inner_productP R mu)) setT G lambda /\
    forall y,C y ->G (gamma y)=y.
Proof.
move=>hChart.
pose X:=inner_metric_space (@euclidean_inner_productP R mu).
pose Y:=inner_metric_space (@euclidean_inner_productP R n).
have hB:=uniform_compact_chart_bilipschitz hChart.
have [g [hg hBound]]:=@metric_bilipschitz_inverse_exists R X Y C gamma lambda (0:X) hB.
pose G:=@euclidean_lipschitz_extension R n mu (gamma @` C) g lambda hBound.
have hG:=@euclidean_lipschitz_extension_specification R n mu (gamma @` C) g lambda hBound.
exists G; split; first exact:kirszbraun_extension_bound_law hG.
move=>y hy.
have hImage:(gamma @` C) (gamma y) by exists y.
rewrite (@kirszbraun_extension_agreement_law R n mu (gamma @` C) g G lambda hG (gamma y) hImage).
exact:(hg y hy).
Qed.
