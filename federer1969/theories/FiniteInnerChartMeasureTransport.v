(** Federer (1969), 3.2.48, p. 284: completed Hausdorff
    measure transport through actual finite-inner coordinates. The
    chart is used through its public inverse and isometry
    laws, retaining all natural degrees and arbitrary source sets. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp
  classical_sets constructive_ereal topology.
From Federer Require Import Hom GrassmannAbbreviations EuclideanInnerProduct InnerProductUP
  InnerMetric FiniteInnerChartUP FiniteInnerChartCompact
  HausdorffMeasure MeasureUP MeasurePushforward PushforwardMeasurableSets.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [finite_inner_chart_hausdorff_pushforward]:
    the exact coordinate measure change of 2.10.11, p. 176,
    used to apply coarea to the inner spaces of 3.2.48,
    p. 284. This is equality of full outer measures. *)
Lemma finite_inner_chart_hausdorff_pushforward (R:realType) (V:lmodType R)
    B (hB:@is_inner_product R V B) N
    (e:Hom (R_n R N) V) (p:Hom V (R_n R N)) q:
  is_finite_inner_chart B e p ->
  measure_pushforward p (@hausdorff_measure R (inner_metric_space hB) q)=
    @hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R N)) q.
Proof.
move=>hChart; apply:funext=>A.
pose S:=p @^-1` A.
have hImage:p @` S=A.
  apply/seteqP; split=>x.
  - by move=>[y hy <-].
  - move=>hx; exists (e x).
    + change (A (p (e x))); by rewrite (finite_inner_chart_left_inverse hChart).
    + exact (finite_inner_chart_left_inverse hChart x).
have h:=@finite_inner_chart_inverse_hausdorff R V B hB N e p hChart q S.
rewrite hImage in h; exact (esym h).
Qed.

(** Source for [finite_inner_chart_coordinates_measurable]:
    completed Hausdorff measurable source sets remain measurable
    in the actual coordinate space, supporting 3.2.48,
    p. 284. This follows from the full image-measure
    equality, not from an identification of completions by topology alone. *)
Lemma finite_inner_chart_coordinates_measurable (R:realType) (V:lmodType R)
    B (hB:@is_inner_product R V B) N
    (e:Hom (R_n R N) V) (p:Hom V (R_n R N)) q (S:set V):
  is_finite_inner_chart B e p ->
  measure_measurable (@hausdorff_measure R (inner_metric_space hB) q) S ->
  measure_measurable (@hausdorff_measure R
    (inner_metric_space (@euclidean_inner_productP R N)) q) (p @` S).
Proof.
move=>hChart hMeas.
rewrite -(@finite_inner_chart_hausdorff_pushforward R V B hB N e p q hChart).
apply:pushforward_measurable_from_preimage.
have hPre:p @^-1` (p @` S)=S.
  apply/seteqP; split=>x.
  - move=>[y hy hpy].
    have hSame:y=x.
      have h:=congr1 e hpy.
      by rewrite !(finite_inner_chart_right_inverse hChart) in h.
    by rewrite -hSame.
  - move=>hx; by exists x.
by rewrite hPre.
Qed.
