(** Federer (1969), 3.2.18, p. 255: choose a compact parameter set
    after extending a near-isometric source piece. The extension's actual
    differential bounds are retained at every chosen point. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import Hom GrassmannAbbreviations EuclideanInnerProduct InnerNorm InnerMetric
  NormDifferentialUP LipschitzUP LipschitzBasic NormMetricScaleContinuity
  MetricBiLipschitzUP MetricBiLipschitzHausdorff MetricBiLipschitzMassTransfer
  KirszbraunExtensionUP KirszbraunExtension RectifiableCompactChartsUP
  LipschitzExtensionDifferentialCore TopologicalBorel BorelFamilyBasic BorelFunctionBasic
  MeasureUP MeasureBasic MeasureAlmostBasic MeasureFiniteClosure MeasureSplit
  BorelRegularMeasureUP HausdorffMeasure EuclideanHausdorffLebesgue
  EuclideanLebesgueDimensions EuclideanLebesgueCompactInner RadonFiniteInnerRegularity.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [compact_chart_from_bilipschitz_piece]: supporting compact
    inner selection in Federer 3.2.18, p. 255, combining 3.2.2,
    2.10.43 and 2.2.3. A compact target subset gives a Borel preimage;
    no preimage measurability is inferred for arbitrary completed-measurable
    target sets. Source density and Rademacher justify the extension's
    differential before compact inner selection. *)
Theorem compact_chart_from_bilipschitz_piece (R : realType) m n
    (S : set (R_n R m)) (h : R_n R m -> R_n R n) (lambda : R)
    (C : set (R_n R n)) :
  @borel_set (inner_metric_space (@euclidean_inner_productP R m)) S ->
  @is_metric_bilipschitz_bound R
    (inner_metric_space (@euclidean_inner_productP R m))
    (inner_metric_space (@euclidean_inner_productP R n)) S h lambda ->
  0<lambda ->
  (forall a, S a -> exists D : Hom (R_n R m) (R_n R n),
    has_norm_differential (inner_norm (@euclidean_inner_productP R m))
      (inner_norm (@euclidean_inner_productP R n)) setT h a D /\
    forall v, lambda^-1*inner_norm (@euclidean_inner_productP R m) v<=
      inner_norm (@euclidean_inner_productP R n) (D v) /\
      inner_norm (@euclidean_inner_productP R n) (D v)<=
        lambda*inner_norm (@euclidean_inner_productP R m) v) ->
  @compact (inner_metric_space (@euclidean_inner_productP R n)) C ->
  C `<=` h @` S ->
  (0<@hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R n)) m C)%E ->
  (@hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R n)) m C< +oo)%E ->
  exists (K : set (R_n R m)) (g : R_n R m -> R_n R n), is_uniform_compact_rectifiable_chart lambda K g /\
    g @` K `<=` C /\
    (0<@hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R n)) m (g @` K))%E.
Proof.
move=> hSB hBi hLam hDeriv hC hCS hCPos hCFin.
pose X := inner_metric_space (@euclidean_inner_productP R m).
pose Y := inner_metric_space (@euclidean_inner_productP R n).
pose mu := @euclidean_lebesgue_measure R m.
have hm := euclidean_lebesgue_is_measure R m.
have hReg := euclidean_lebesgue_borel_regular R m.
pose g := @euclidean_lipschitz_extension R m n S h lambda hBi.1.
have hg := @euclidean_lipschitz_extension_specification R m n S h lambda hBi.1.
have hAgree x (hx : S x) : g x=h x.
  exact: (@kirszbraun_extension_agreement_law R m n S h g lambda hg x hx).
have hGlobal : @is_metric_lipschitz_bound R X Y setT g lambda.
  exact: kirszbraun_extension_bound_law hg.
have hCont : continuous (fun x : X=>(g x:Y)).
  apply: (@metric_fixed_lipschitz_continuous R X Y g lambda (ltW hLam)).
  by move=> x y; exact: hGlobal.2 x y I I.
have hGBi : @is_metric_bilipschitz_bound R X Y S g lambda.
  split; first exact: (metric_lipschitz_bound_restrict (fun _ _=>I) hGlobal).
  move=> x y hx hy; rewrite (hAgree x hx) (hAgree y hy).
  exact: hBi.2 x y hx hy.
pose A := S `&` (g @^-1` C).
have hCB : @borel_set Y C := closed_borel_set (compact_closed (@metric_hausdorff R Y) hC).
have hAB : @borel_set X A.
  exact: (@borel_family_binary_intersection X setT _ (borel_sets_family X) S (g @^-1` C) hSB
    (borel_function_preimage (continuous_borel_function hCont) hCB)).
have hAm : measure_measurable mu A := borel_regular_borel_measurable hm hReg hAB.
have hAS : A `<=` S by move=> x hx; exact hx.1.
have hImage : g @` A=C.
  apply/seteqP; split.
  - by move=> y [x [_ hx] <-].
  - move=> y hy; have [x hx hxy] := hCS y hy.
    exists x; last by rewrite (hAgree x hx).
    split=> //; change (C (g x)); by rewrite (hAgree x hx) hxy.
have hImgPos : (0<@hausdorff_measure R Y m (g @` A))%E by rewrite hImage.
have hImgFin : (@hausdorff_measure R Y m (g @` A)< +oo)%E by rewrite hImage.
have [hAPos hAFin] := @metric_bilipschitz_finite_positive_transfer R X Y S A g lambda m 0
  hGBi hAS hLam hImgPos hImgFin.
rewrite (euclidean_hausdorff_spherical_lebesgue A).1 in hAPos hAFin.
have hSm : measure_measurable mu S := borel_regular_borel_measurable hm hReg hSB.
have [T [hTS [hTm [hLoss hGood]]]] := @lipschitz_extension_uniform_differential_core R m n
  S h g lambda hSm hGlobal (fun x hx=>esym (hAgree x hx)) hDeriv.
pose B := A `&` T.
have hBm : measure_measurable mu B := measure_measurable_intersection hm hAm hTm.
have hBA : B `<=` A by move=> x hx; exact hx.1.
have hBFin : (mu B< +oo)%E := le_lt_trans (measure_mono hm hBA) hAFin.
have hNull : mu (A `\` B)=0%E.
  apply: (measure_null_subset hm _ hLoss)=> x [hx hn].
  split; first exact: hAS x hx.
  move=> ht; apply: hn; by split.
have hABBound : (mu A<=mu B)%E.
  have hCover : A `<=` B `|` (A `\` B).
    move=> x hx; case: (pselect (B x))=> hb; [by left|by right; split].
  have hh := measure_binary_cover hm hCover.
  change (is_true (mu A<=mu B+mu (A `\` B))%E) in hh.
  by rewrite hNull adde0 in hh.
have hBPos : (0<mu B)%E := lt_le_trans hAPos hABBound.
have [K [hK [hKB hKPos]]] := @radon_positive_compact_subset R X mu hm
  (euclidean_lebesgue_radon R m) B hBm hBFin hBPos.
have hKS : K `<=` S by move=> x hx; exact: hAS x (hKB x hx).1.
have hKA : K `<=` A by move=> x hx; exact: (hKB x hx).1.
have hChart : is_uniform_compact_rectifiable_chart lambda K g.
  constructor=> //.
  - by move=> x y hx hy; exact: hGBi.2 x y (hKS x hx) (hKS y hy).
  - by move=> a ha; exact: hGood a (hKB a ha).2.
exists K,g; split; first exact hChart.
split; first by move=> y [x hx <-]; exact: (hKA x hx).2.
have hInv := (@metric_bilipschitz_hausdorff_bounds R X Y S g lambda 0 m K hGBi hKS).2.
rewrite (euclidean_hausdorff_spherical_lebesgue K).1 in hInv.
rewrite ltNge; apply/negP=> hZeroLe.
have hZero : @hausdorff_measure R Y m (g @` K)=0%E.
  apply/eqP; rewrite eq_le hZeroLe (measure_nonnegative (@hausdorff_measure_is_measure R Y m)); reflexivity.
rewrite hZero mule0 in hInv.
by have := lt_le_trans hKPos hInv; rewrite ltxx.
Qed.
