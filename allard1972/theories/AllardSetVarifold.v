(** Allard (1972), 3.5, p. 431, blueprint al:3.5 and al:3.5:lem: the
    varifold v(E) of a set E ⊆ R^n which is H^k measurable and meets every
    compact set in an (H^k, k) rectifiable set. We use Allard's own formula
    v(E)(A) = H^k(E ∩ {x : (x, Tan^k(H^k⌞E, x)) ∈ A}) for all
    A ⊆ G_k(R^n), and prove that it is a Radon measure. The blueprint
    al:3.5 defines v(E) as the Borel regular measure with these values on
    Borel sets; by blueprint rem:3.5 the two agree on all sets, which is
    the content of [set_varifold_measure_regular]. Its proof uses a Borel
    version t of the tangent plane map (Federer 2.3.6, p. 77): v(E) is the
    image of H^k⌞E under [x ↦ (x, t(x))], and Borel regularity follows from
    the Borel measurability of the graph of t (Federer 2.2.14, p. 70).
    Consequences: ‖v(E)‖ = H^k⌞E as measures, and the integral formula
    v(E)(f) = ∫_E f(x, Tan^k(H^k⌞E, x)) dH^k x for real Borel f. Here
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
  MeasurableGraphEquivalence ExtendedRealOrderTopology RealMetricBackground.
From Allard Require Import AllardOrthogonalProjectors AllardGrassmann AllardGrassmannSubspaces
  AllardVarifolds AllardRectifiableVarifolds AllardTangentMeasurability.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section SetVarifold.
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

(** Source for [set_varifold]: Allard 3.5, p. 431: v(E)(A) = H^k(E ∩ {x :
    (x, Tan^k(H^k⌞E, x)) ∈ A}) for A ⊆ G_k(R^n), Allard's own formula
    (blueprint rem:3.5; the blueprint al:3.5 uses the Borel regular measure
    with the same Borel values). Definition. *)
Definition set_varifold (E : set RnM) : set GB -> \bar R := fun A => HK (pre E A).

Local Notation vE E := (set_varifold E).

(** Source for [set_varifold_pushforward]: Allard 3.5, p. 431, with Federer
    2.1.2, p. 54: if t is a map of R^n into G(n, k) agreeing with g_E H^k⌞E
    almost everywhere, then v(E) is the image of H^k⌞E under [x ↦ (x, t(x))].
    Supporting lemma. *)
Lemma set_varifold_pushforward E (t : RnM -> GA) :
  measure_almost_equal (measure_restrict HK E) (tau (measure_restrict HK E)) (partial_function_total t) ->
  set_varifold E = measure_pushforward (fun x : RnM => ((x, t x) : GB)) (measure_restrict HK E).
Proof.
move=> ht; have [hHm _] := @hausdorff_measure_laws R n k.
apply: funext=> A; rewrite /set_varifold /measure_pushforward /measure_restrict.
have h0 : HK (E `&` ~` partial_function_agreement (tau (measure_restrict HK E))
    (partial_function_total t)) = 0 := ht.
apply: (measure_null_modification_value hHm h0)=> x hx.
have hag : E x -> partial_function_agreement (tau (measure_restrict HK E)) (partial_function_total t) x.
  move=> hEx; case: (pselect (partial_function_agreement (tau (measure_restrict HK E))
    (partial_function_total t) x))=> // hn.
  by exfalso; apply: hx; split.
split.
- move=> [hEx [S [hS hA]]]; split=> //.
  have [y [hy hty]] := hag hEx.
  have e := partial_function_single_valued hS hy.
  by rewrite /= hty -e.
- move=> [hEx hA]; split=> //.
  have [y [hy hty]] := hag hEx.
  by exists y; split=> //; rewrite -hty.
Qed.

(** Source for [set_varifold_zero]: v(E) = 0 when G(n, k) is empty.
    Supporting lemma. *)
Lemma set_varifold_zero E : (forall S : GA, False) -> set_varifold E = fun=> 0%E.
Proof.
move=> hno; have [hHm _] := @hausdorff_measure_laws R n k.
apply: funext=> A; rewrite /set_varifold.
have -> : pre E A = set0 by apply/seteqP; split=> x // [_ [S _]]; exact: hno S.
exact: measure_empty hHm.
Qed.

(** Source for [pushforward_preimage_measurable]: Federer 2.1.2, p. 54: if
    f^{-1}[A] is μ measurable, then A is f_# μ measurable. Supporting lemma. *)
Lemma pushforward_preimage_measurable (f : RnM -> GB) (mu : set RnM -> \bar R) (A : set GB) :
  measure_measurable mu (f @^-1` A) -> measure_measurable (measure_pushforward f mu) A.
Proof. by move=> h T; exact: h (f @^-1` T). Qed.

(** Source for [graph_map_borel]: Federer 2.2.10, p. 65, and 2.3.2(5), p.
    73: [x ↦ (x, t(x))] is a Borel map into G_k(R^n) = R^n × G(n, k) whenever
    t is a Borel map into G(n, k). Supporting lemma. *)
Lemma graph_map_borel (t : RnM -> GA) :
  is_borel_function t -> is_borel_function (fun x : RnM => ((x, t x) : GB)).
Proof.
move=> ht.
have [U hU] := @inner_space_countable_open_base R Rn _ hBn n _ hbn.
have [V hV] := @compact_metric_countable_open_base R GA (@projection_grassmann_compact R n k).
have h := @borel_pair_function RnM RnM GA (fun x => x) t U V hU hV
  (continuous_borel_function (fun x : RnM => @cvg_id _ (nbhs x))) ht.
exact h.
Qed.

(** Source for [pushforward_graph_borel_regular]: Federer 2.2.3, p. 61, and
    2.2.14, p. 70 (the graph of a Borel map is a Borel set): the image of
    H^k⌞E under [x ↦ (x, t(x))], t Borel, is a Borel regular measure over
    G_k(R^n). Supporting lemma. *)
Lemma pushforward_graph_borel_regular E (t : RnM -> GA) : locrect E -> is_borel_function t ->
  is_borel_regular_measure (measure_pushforward (fun x : RnM => ((x, t x) : GB)) (measure_restrict HK E)).
Proof.
move=> hE ht; have [hHm hHr] := @hausdorff_measure_laws R n k.
pose g := fun x : RnM => ((x, t x) : GB).
have hg : is_borel_function g := graph_map_borel ht.
have hfst : is_borel_function (@grassmann_bundle_point R n k).
  exact: continuous_borel_function (@grassmann_bundle_point_continuous R n k).
constructor.
- move=> U hU; apply: pushforward_preimage_measurable; apply: measure_restrict_measurable.
  apply: (borel_regular_borel_measurable hHm hHr).
  exact: borel_function_preimage hg _ (open_borel_set hU).
- move=> A.
  have [C [hAC [hC heq]]] := borel_regular_cover hHr (E `&` g @^-1` A).
  have [D [B [hD hB hDE hEB h0]]] := locally_rectifiable_borel_sandwich hE.
  pose Bs := ([set z : GB | C z.1] `|` [set z : GB | ~ D z.1]) `|` ~` [set z : GB | t z.1 = z.2].
  have hABs : A `<=` Bs.
    move=> z hz.
    case: (pselect (C z.1))=> h1; first by left; left.
    case: (pselect (D z.1))=> h2; last by left; right.
    case: (pselect (t z.1 = z.2))=> h3; last by right.
    exfalso; apply: h1; apply: hAC; split; first exact: hDE _ h2.
    rewrite /g /= h3; by case: z hz {h2 h3}.
  exists Bs; split; [exact: hABs|split].
  + apply: borel_setU; first apply: borel_setU.
    * exact: borel_function_preimage hfst _ hC.
    * exact: borel_function_preimage hfst _ (borel_set_complement hD).
    * apply: borel_set_complement.
      have h := @borel_function_graph R RnM GA t (@projection_grassmann_separable R n k) ht.
      exact h.
  + rewrite /measure_pushforward /measure_restrict.
    apply/eqP; rewrite eq_le; apply/andP; split.
    * apply: (measure_mono hHm)=> x [hEx hx]; split=> //; exact: hABs _ hx.
    * rewrite heq.
      have hc := @measure_binary_cover R RnM HK hHm (E `&` g @^-1` Bs) C (B `\` D).
      rewrite h0 adde0 in hc; apply: hc.
      move=> x [hEx [[h1|h2]|h3]]; [by left|right; split=> //; exact: hEB|].
      by exfalso; apply: h3.
Qed.

(** Source for [zero_measure_facts]: the zero measure over G_k(R^n) is a
    Borel regular measure. Supporting lemma. *)
Lemma zero_measure_facts : is_measure (fun _ : set GB => (0 : \bar R)) /\ is_borel_regular_measure (fun _ : set GB => (0 : \bar R)).
Proof.
split.
- constructor; first by move=> A; exact: lexx.
  move=> A F _ _; exact: nonnegative_sum_nonnegative.
- constructor.
  + by move=> U _ T; rewrite adde0.
  + move=> A; exists setT; split=> //; split=> //; exact: open_borel_set openT.
Qed.

(** Source for [set_varifold_measure_regular]: blueprint al:3.5:lem: v(E) is
    a Borel regular measure over G_k(R^n). Supporting lemma. *)
Lemma set_varifold_measure_regular E : locrect E ->
  is_measure (vE E) /\ is_borel_regular_measure (vE E).
Proof.
move=> hE; have [hHm hHr] := @hausdorff_measure_laws R n k.
case: (pselect (exists S0 : GA, True)) => [[S0 _]|hno].
- have [t [ht hae]] := set_tangent_borel_version S0 hE.
  rewrite (set_varifold_pushforward hae); split.
  + exact: measure_pushforward_is_measure (measure_restrict_is_measure hHm E).
  + exact: pushforward_graph_borel_regular hE ht.
- rewrite set_varifold_zero; first exact: zero_measure_facts.
  by move=> S; apply: hno; exists S.
Qed.

(** Source for [set_varifold_preimage_subset]: Allard 3.5, p. 431: {x : (x,
    Tan^k(H^k⌞E, x)) ∈ A} ∩ E ⊆ E ∩ π[A]. Supporting lemma. *)
Lemma set_varifold_preimage_subset E A : pre E A `<=` E `&` (g1 @` A).
Proof. by move=> x [hEx [S [_ hA]]]; split=> //; exists (x, S). Qed.

(** Source for [set_varifold_compact_finite]: blueprint al:3.5:lem, proof:
    v(E)(C) ≤ H^k(E ∩ π[C]) < ∞ for compact C ⊆ G_k(R^n). Supporting lemma. *)
Lemma set_varifold_compact_finite E K : locrect E -> compact K -> (vE E K < +oo)%E.
Proof.
move=> hE hK; have [hHm _] := @hausdorff_measure_laws R n k; have [_ hEr] := hE.
have hc : compact (g1 @` K).
  exact: continuous_compact (continuous_subspaceT (@grassmann_bundle_point_continuous R n k)) hK.
apply: le_lt_trans (hEr _ hc).2.
rewrite /set_varifold; apply: (measure_mono hHm); exact: set_varifold_preimage_subset.
Qed.

(** Source for [set_varifold_is_varifold]: Allard 3.5, p. 431, blueprint
    al:3.5:lem: v(E) ∈ V_k(R^n), that is, v(E) is a Radon measure over
    G_k(R^n) (Federer 2.2.5, p. 62; the countable criterion of 2.2.16).
    Direct formalisation. *)
Theorem set_varifold_is_varifold E : locrect E -> is_varifold (vE E).
Proof.
move=> hE; have [hm hr] := set_varifold_measure_regular hE.
have [hHm _] := @hausdorff_measure_laws R n k.
split=> //.
pose C (j : nat) : set GB := ball j `*` [set: GA].
pose W (j : nat) : set GB := [set z : GB | mdist (0 : RnM) z.1 < j%:R].
apply: (@countable_locally_finite_metric_radon R GB _ C W hm hr).
- exact: (@grassmann_bundle_locally_compact R n k).
- by move=> K hK; exact: set_varifold_compact_finite.
- move=> j; apply: compact_setX.
  + exact: (@euclidean_closed_metric_ball_compact R n (0 : RnM) j%:R).
  + exact: (@projection_grassmann_compact R n k).
- by move=> z _; have [j hj] := closed_ball_cover z.1; exists j.
- move=> j; split.
  + apply: (@open_comp GB RnM g1 [set x | mdist (0 : RnM) x < j%:R]).
      by move=> z _; exact: (@grassmann_bundle_point_continuous R n k z).
    exact: metric_open_ball_open.
  + apply: le_lt_trans (locally_rectifiable_ball_finite j hE).
    apply: (measure_mono hHm)=> x [hEx [S [_ hS]]]; split=> //.
    rewrite /metric_closed_ball /=; exact: ltW hS.
- move=> z _; exists (Num.bound (mdist (0 : RnM) z.1)) => //.
  exact: archi_boundP (mdist_ge0 _ _).
Qed.

(** Source for [set_varifold_set_varifold]: Allard 3.5, p. 431: v(E) has the
    characteristic property [is_set_varifold] of section 3
    (AllardRectifiableVarifolds.v). Direct formalisation. *)
Theorem set_varifold_set_varifold E : locrect E -> is_set_varifold E (vE E).
Proof. by move=> hE; constructor; [exact: set_varifold_is_varifold|move=> B _]. Qed.

(** Source for [set_varifold_weight]: Allard 3.5, p. 431, blueprint
    al:3.5:lem: ‖v(E)‖ = H^k⌞E, as measures over R^n (equality on all sets).
    Direct formalisation. *)
Theorem set_varifold_weight E : locrect E -> varifold_weight (vE E) = measure_restrict HK E.
Proof.
move=> hE; have [hHm _] := @hausdorff_measure_laws R n k.
have h0 := @set_approximate_tangent_plane_ae R n k E hE.
apply: funext=> A; rewrite varifold_weightE /set_varifold /measure_restrict.
apply: (measure_null_modification_value hHm h0)=> x hx; split.
- by move=> [hEx [S [_ hA]]].
- move=> [hEx hA]; split=> //.
  case: (pselect (exists S, partial_function_graph (tau (measure_restrict HK E)) x S))=> [[S hS]|hn].
  + by exists S.
  + by exfalso; apply: hx; split.
Qed.

(** Source for [projection_grassmann_point]: Allard 2.3, p. 421: G(n, k) is
    nonempty whenever k ≤ n; the orthogonal projection onto the span of the
    first k coordinate vectors belongs to it. Supporting lemma. *)
Lemma projection_grassmann_point : (k <= n)%N -> exists S : GA, True.
Proof.
move=> hkn.
pose u (i : 'I_k) : Rn := @coordinate_basis R n (widen_ord hkn i).
have hu : orthonormal_family (@euclidean_inner_product R n) u.
  move=> i j; rewrite /u euclidean_inner_basis /coordinate_basis ffunE.
  case: eqP=> h; case: eqP=> h' //.
  - by exfalso; apply: h'; apply: val_inj; have := congr1 val h.
  - by exfalso; apply: h; rewrite h'.
have hP := @frame_projector_orthogonal_projector R Rn _ hBn n _ hbn k u hu.
by exists (projection_grassmann_of hP).
Qed.

(** Source for [set_tangent_integrand_graph]: Allard 3.5, p. 431: the graph
    of [x ↦ f(x, Tan^k(H^k⌞E, x))], defined where the approximate tangent
    plane exists. Definition. *)
Definition set_tangent_integrand_graph (E : set RnM) (f : GB -> R) (x : RnM) (a : \bar R) : Prop :=
  exists S, partial_function_graph (tau (measure_restrict HK E)) x S /\ a = (f (x, S))%:E.

(** Source for [set_tangent_integrand_functional]: the graph
    [set_tangent_integrand_graph] is single valued. Supporting lemma. *)
Lemma set_tangent_integrand_functional (E : set RnM) (f : GB -> R) x a b :
  set_tangent_integrand_graph E f x a -> set_tangent_integrand_graph E f x b -> a = b.
Proof.
move=> [S [hS ->]] [S' [hS' ->]].
by rewrite (partial_function_single_valued hS hS').
Qed.

(** Source for [set_tangent_integrand]: Allard 3.5, p. 431: the partial
    integrand [x ↦ f(x, Tan^k(H^k⌞E, x))] over R^n. Definition. *)
Definition set_tangent_integrand (E : set RnM) (f : GB -> R) : partial_function RnM (extended_real_line R) :=
  @Build_partial_function RnM (extended_real_line R) (set_tangent_integrand_graph E f)
    (@set_tangent_integrand_functional E f).

(** Source for [set_varifold_integral]: Allard 3.5, p. 431, blueprint
    al:3.5:lem: v(E)(f) = ∫_E f(x, Tan^k(H^k⌞E, x)) dH^k x for every real
    valued Borel function f on G_k(R^n), as an equivalence of integral
    values (either side may be infinite or undefined; Federer 2.4.2, p. 81,
    and 2.4.18, p. 90). Allard's standing hypothesis k ≤ n supplies a point
    of G(n, k). Direct formalisation. *)
Theorem set_varifold_integral E (f : GB -> R) : (k <= n)%N -> locrect E ->
  is_borel_function (f : GB -> real_line_metric R) -> forall a,
  is_measure_integral (vE E) (real_total_integrand f) a <->
  is_measure_integral (measure_restrict HK E) (set_tangent_integrand E f) a.
Proof.
move=> hkn hE hf a.
have [hHm hHr] := @hausdorff_measure_laws R n k.
have hm := measure_restrict_is_measure hHm E.
have hr := locally_rectifiable_restrict_borel_regular hE.
have [S0 _] := projection_grassmann_point hkn.
have [t [ht hae]] := set_tangent_borel_version S0 hE.
pose g := fun x : RnM => ((x, t x) : GB).
rewrite (set_varifold_pushforward hae).
have hfg : is_borel_function ((fun x => f (g x)) : RnM -> real_line_metric R).
  exact: (borel_function_composition (graph_map_borel ht) hf).
have hpre : is_measure_measurable_function (measure_restrict HK E)
    (partial_function_precompose g (real_total_integrand f)).
  apply: (@measurable_function_graph_equivalent R RnM _ _
    (real_total_integrand ((fun x => f (g x)) : RnM -> R))); first by [].
  apply: (@measurable_partial_real_embedding R RnM _ hm).
  exact: (@borel_map_measure_measurable R RnM (real_line_metric R) _ _ hm hr hfg).
rewrite -(@measure_pushforward_integral_iff R RnM GB _ hm g (real_total_integrand f) hpre a).
have hag x : E x -> partial_function_agreement (tau (measure_restrict HK E)) (partial_function_total t) x ->
    partial_function_agreement (partial_function_precompose g (real_total_integrand f))
      (set_tangent_integrand E f) x.
  move=> hEx [y [hy hty]]; exists (f (x, y))%:E; split.
  - by exists (f (g x)); split=> //; rewrite /g /= hty.
  - by exists y.
have hae1 : measure_almost_equal (measure_restrict HK E)
    (partial_function_precompose g (real_total_integrand f)) (set_tangent_integrand E f).
  rewrite /measure_almost_equal /measure_almost_everywhere /measure_restrict.
  apply: (measure_null_subset hHm _ hae)=> x [hEx hn]; split=> // h; apply: hn; exact: hag.
have hae2 : measure_almost_equal (measure_restrict HK E)
    (set_tangent_integrand E f) (partial_function_precompose g (real_total_integrand f)).
  rewrite /measure_almost_equal /measure_almost_everywhere /measure_restrict.
  apply: (measure_null_subset hHm _ hae)=> x [hEx hn]; split=> // h; apply: hn.
  have [z [h1 h2]] := hag x hEx h; by exists z.
split=> h.
- exact: (@measure_integral_almost_equal R RnM _ hm _ _ a h hae1).
- exact: (@measure_integral_almost_equal R RnM _ hm _ _ a h hae2).
Qed.


End SetVarifold.
