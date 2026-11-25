(** Allard (1972), 3.5(1)(b), p. 432: for V = Σ_i c_i v(E_i) with
    weight μ = Σ_i c_i H^k⌞E_i, if Tan^k(μ, ·) is μ measurable and agrees
    with Tan^k(H^k⌞E_i, ·) at H^k almost all points of E_i, then V is the
    image of μ under [x ↦ (x, Tan^k(μ, x))] and
    V(f) = ∫ f(x, Tan^k(μ, x)) dμ x for real valued Borel f. The proof uses
    a Borel version of Tan^k(μ, ·) (Federer 2.3.6, p. 77). Here
    M = U = R^n. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets functions reals
  constructive_ereal topology normedtype lra cardinality.
From Federer Require Import ModuleQuotient GrassmannAbbreviations EuclideanInnerProduct EuclideanLinearMaps
  InnerNorm InnerMetric NormMetric HilbertFormCompactness LinearBasis FiniteCoordinates Hom HomInner
  GrassmannSubspaces PartialFunctionUP PartialFunctionBasic PartialFunctionPostcomposition
  PartialFunctionPrecomposition MeasureUP MeasureBasic MeasureAlmostUP MeasureAlmostBasic
  MeasureRestriction RadonMeasureUP BorelRegularMeasureUP TopologicalBorel BorelFunctionUP
  BorelFunctionBasic HausdorffMeasure HausdorffClosedCoverAgreement MetricClosedBalls
  EuclideanClosedBallCompact MeasurableFunctionUP MeasureApproximateTangentUP RectifiableTangentPlaneUP
  RectifiableSetUP MeasureFiniteClosure MeasureCountableClosure MeasureNullModification
  MeasurePushforward MeasureSplit NonnegativeSum BorelProductMaps BorelGraphs InnerSpaceCountableBase
  CompactMetricSeparability CountableOpenBaseUP CountableLocalFiniteMetricRadon MeasureIntegralUP
  MeasureIntegralAlmostEquality SummableRealFunctionUP MeasureStepIntegralIdentification
  PushforwardIntegral BVCurveMeasurable OrthonormalFamilies CoordinateProjection
  MeasurableGraphEquivalence ExtendedRealOrderTopology RealMetricBackground
  LusinBorelVersion RadonBorelRegularity CountablyMeasurableUP NonnegativeSumSupport.
From Allard Require Import AllardOrthogonalProjectors AllardGrassmann AllardGrassmannSubspaces
  AllardVarifolds AllardRectifiableVarifolds AllardTangentMeasurability
  AllardSetVarifold AllardRectifiableSum.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section RectifiableIntegral.
Variable R : realType.
Variables n k : nat.
Local Notation Rn := (R_n R n).
Local Notation hBn := (@euclidean_inner_productP R n).
Local Notation hbn := (@coordinate_basisP R n).
Local Notation RnM := (inner_metric_space hBn).
Local Notation GA := (projection_grassmann R n k).
Local Notation GB := (grassmann_bundle R n k).
Local Notation HK := (@hausdorff_measure R RnM k).
Local Notation tau mu := (@approximate_tangent_plane R n k mu).
Local Notation locrect E := (@is_locally_rectifiable_set R n k E).
Local Notation pre E A := (@set_varifold_preimage R n k E A).
Local Notation ball j := (metric_closed_ball (0 : RnM) (j%:R)).
Local Notation g1 := (@grassmann_bundle_point R n k).


Variables (c : nat -> R) (E : nat -> set RnM).
Hypothesis hc : forall i, 0 < c i.
Local Notation mu := (@rectifiable_sum_measure R n k c E).

(** Source for [rectifiable_sum_component_null]: Allard 3.5, p. 431, with
    Federer 2.1.2, p. 54: since c_i > 0, a set N with
    Σ_i c_i H^k(E_i ∩ N) = 0 satisfies H^k(E_i ∩ N) = 0 for every i.
    Supporting lemma. *)
Lemma rectifiable_sum_component_null (N : set RnM) i : mu N = 0%E -> HK (E i `&` N) = 0%E.
Proof.
move=> h0; have [hHm _] := @hausdorff_measure_laws R n k.
have ht : ((c i)%:E * HK (E i `&` N) <= mu N)%E :=
  @nonnegative_sum_term R _ [set: nat] (fun i => ((c i)%:E * HK (E i `&` N))%E) i Logic.I.
rewrite h0 in ht.
apply/eqP; rewrite eq_le (measure_nonnegative hHm) andbT.
rewrite leNgt; apply/negP=> hpos.
have hci : (0 < (c i)%:E)%E by rewrite lte_fin; exact: hc.
by have := mule_gt0 hci hpos; rewrite ltNge ht.
Qed.

Hypotheses (hm : is_measure mu) (hr : is_radon_measure mu).

(** Source for [rectifiable_sum_countably_measurable]: Federer 2.3.6,
    p. 77, hypothesis: R^n is the union of countably many μ measurable sets
    of finite μ measure, the closed balls B(0, j), for a Radon measure μ
    over R^n (Federer 2.2.5, p. 61). Supporting lemma. *)
Lemma rectifiable_sum_countably_measurable : measure_countably_measurable mu setT.
Proof.
have hb := radon_borel_regular hm hr.
exists ((fun j : nat => ball j) @` setT); split; [|split].
- exact: (card_le_trans (card_image_le _ _) (countableP [set: nat])).
- apply/seteqP; split=> // x _; have [j hj] := @closed_ball_cover R n x.
  by exists (ball j) => //; exists j.
- move=> _ [j _ <-]; split.
  + apply: (borel_regular_borel_measurable hm hb).
    exact: closed_borel_set (@metric_closed_ball_closed R RnM (0 : RnM) j%:R).
  + exact: (radon_compact_finite hr (@euclidean_closed_metric_ball_compact R n (0 : RnM) j%:R)).
Qed.

Hypothesis hagree : forall i, measure_almost_everywhere_on HK (E i)
  (partial_function_agreement (tau mu) (tau (measure_restrict HK (E i)))).
Hypothesis hmeas : is_measure_measurable_function mu (tau mu).

(** Source for [rectifiable_sum_tangent_borel_version]: Federer 2.3.6,
    p. 77, first corollary: Tan^k(μ, ·) agrees μ almost everywhere with a
    Borel map t of R^n into G(n, k); by the hypothesis [hagree], t agrees
    with Tan^k(H^k⌞E_i, ·) at H^k almost all points of E_i. Supporting
    lemma. *)
Lemma rectifiable_sum_tangent_borel_version (S0 : GA) :
  exists t : RnM -> GA, is_borel_function t /\
    measure_almost_equal mu (tau mu) (partial_function_total t) /\
    forall i, measure_almost_equal (measure_restrict HK (E i)) (tau (measure_restrict HK (E i)))
      (partial_function_total t).
Proof.
have [hHm _] := @hausdorff_measure_laws R n k.
have [D [hDc hDd]] := @projection_grassmann_separable R n k.
have [t [ht hae]] := @lusin_borel_version_radon R RnM GA mu hm hr D (tau mu) S0 hDc hDd hmeas
  rectifiable_sum_countably_measurable.
exists t; split=> //; split=> // i.
have h1 := rectifiable_sum_component_null i hae.
have h2 := hagree i.
rewrite /measure_almost_equal /measure_almost_everywhere /measure_restrict.
have h0 : HK ((E i `&` ~` partial_function_agreement (tau mu) (partial_function_total t)) `|`
    (E i `\` partial_function_agreement (tau mu) (tau (measure_restrict HK (E i))))) = 0%E.
  apply: (measure_null_union hHm)=> //.
apply: (measure_null_subset hHm _ h0)=> x [hEx hn].
case: (pselect (partial_function_agreement (tau mu) (partial_function_total t) x))=> h; last by left.
case: (pselect (partial_function_agreement (tau mu) (tau (measure_restrict HK (E i))) x))=> h'; last by right.
exfalso; apply: hn.
have [y [hy hty]] := h; have [z [hz hz']] := h'.
have e := partial_function_single_valued hy hz.
by exists z; split=> //; rewrite /= hty e.
Qed.

(** Source for [rectifiable_varifold_pushforward]: Allard 3.5, p. 431, with
    Federer 2.1.2, p. 54: if t agrees with Tan^k(H^k⌞E_i, ·) at H^k almost
    all points of E_i for every i, then Σ_i c_i v(E_i) is the image of
    μ = Σ_i c_i H^k⌞E_i under [x ↦ (x, t(x))]. Direct formalisation. *)
Theorem rectifiable_varifold_pushforward (V : set GB -> \bar R) (t : RnM -> GA) :
  (forall A, V A = nonnegative_sum [set: nat] (fun i => ((c i)%:E * set_varifold (E i) A)%E)) ->
  (forall i, measure_almost_equal (measure_restrict HK (E i)) (tau (measure_restrict HK (E i)))
    (partial_function_total t)) ->
  V = measure_pushforward (fun x : RnM => ((x, t x) : GB)) mu.
Proof.
move=> hV ht; apply: funext=> A; rewrite hV /measure_pushforward /rectifiable_sum_measure.
apply: nonnegative_sum_ext=> i _.
by rewrite (set_varifold_pushforward (ht i)).
Qed.

(** Source for [measure_tangent_integrand_graph]: Allard 3.5(1)(b),
    p. 432: the graph of [x ↦ f(x, Tan^k(ν, x))] for a measure ν over R^n,
    defined where Tan^k(ν, x) ∈ G(n, k). Definition. *)
Definition measure_tangent_integrand_graph (nu : set RnM -> \bar R) (f : GB -> R) (x : RnM) (a : \bar R) : Prop :=
  exists S, partial_function_graph (tau nu) x S /\ a = (f (x, S))%:E.

(** Source for [measure_tangent_integrand_functional]: the graph
    [measure_tangent_integrand_graph] is single valued. Supporting lemma. *)
Lemma measure_tangent_integrand_functional (nu : set RnM -> \bar R) (f : GB -> R) x a b :
  measure_tangent_integrand_graph nu f x a -> measure_tangent_integrand_graph nu f x b -> a = b.
Proof.
move=> [S [hS ->]] [S' [hS' ->]].
by rewrite (partial_function_single_valued hS hS').
Qed.

(** Source for [measure_tangent_integrand]: Allard 3.5(1)(b), p. 432: the
    partial integrand [x ↦ f(x, Tan^k(ν, x))] over R^n. Definition. *)
Definition measure_tangent_integrand (nu : set RnM -> \bar R) (f : GB -> R) :
    partial_function RnM (extended_real_line R) :=
  @Build_partial_function RnM (extended_real_line R) (measure_tangent_integrand_graph nu f)
    (@measure_tangent_integrand_functional nu f).

(** Source for [rectifiable_varifold_integral]: Allard 3.5(1)(b), p. 432,
    with Federer 2.4.18, p. 90: V(f) = ∫ f(x, Tan^k(μ, x)) dμ x for
    V = Σ_i c_i v(E_i), μ = Σ_i c_i H^k⌞E_i and every real valued Borel
    function f on G_k(R^n), as an equivalence of integral values (Federer
    2.4.2, p. 81). Allard's standing hypothesis k ≤ n supplies a point of
    G(n, k). Direct formalisation under the hypotheses of the section. *)
Theorem rectifiable_varifold_integral (V : set GB -> \bar R) (f : GB -> R) : (k <= n)%N ->
  (forall A, V A = nonnegative_sum [set: nat] (fun i => ((c i)%:E * set_varifold (E i) A)%E)) ->
  is_borel_function (f : GB -> real_line_metric R) -> forall a,
  is_measure_integral V (real_total_integrand f) a <->
  is_measure_integral mu (measure_tangent_integrand mu f) a.
Proof.
move=> hkn hV hf a.
have hb := radon_borel_regular hm hr.
have [S0 _] := @projection_grassmann_point R n k hkn.
have [t [ht [hae hi]]] := rectifiable_sum_tangent_borel_version S0.
pose g := fun x : RnM => ((x, t x) : GB).
rewrite (rectifiable_varifold_pushforward hV hi).
have hfg : is_borel_function ((fun x => f (g x)) : RnM -> real_line_metric R).
  exact: (borel_function_composition (graph_map_borel ht) hf).
have hpre : is_measure_measurable_function mu (partial_function_precompose g (real_total_integrand f)).
  apply: (@measurable_function_graph_equivalent R RnM _ _
    (real_total_integrand ((fun x => f (g x)) : RnM -> R))); first by [].
  apply: (@measurable_partial_real_embedding R RnM _ hm).
  exact: (@borel_map_measure_measurable R RnM (real_line_metric R) _ _ hm hb hfg).
rewrite -(@measure_pushforward_integral_iff R RnM GB _ hm g (real_total_integrand f) hpre a).
have hag x : partial_function_agreement (tau mu) (partial_function_total t) x ->
    partial_function_agreement (partial_function_precompose g (real_total_integrand f))
      (measure_tangent_integrand mu f) x.
  move=> [y [hy hty]]; exists (f (x, y))%:E; split.
  - by exists (f (g x)); split=> //; rewrite /g /= hty.
  - by exists y.
have hae1 : measure_almost_equal mu
    (partial_function_precompose g (real_total_integrand f)) (measure_tangent_integrand mu f).
  apply: (measure_null_subset hm _ hae)=> x hn h; apply: hn; exact: hag.
have hae2 : measure_almost_equal mu
    (measure_tangent_integrand mu f) (partial_function_precompose g (real_total_integrand f)).
  apply: (measure_null_subset hm _ hae)=> x hn h; apply: hn.
  have [z [h1 h2]] := hag x h; by exists z.
split=> h.
- exact: (@measure_integral_almost_equal R RnM _ hm _ _ a h hae1).
- exact: (@measure_integral_almost_equal R RnM _ hm _ _ a h hae2).
Qed.
End RectifiableIntegral.
