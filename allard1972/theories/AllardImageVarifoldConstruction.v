(** Allard (1972), 3.2(1), printed p. 430, specialised to M = M' = R^n;
    blueprint al:3.2. Existence of the image varifold F_# V: under the
    hypotheses of [is_proper_class_one_immersion], the measure

        F_♮ # (V ⌞ J),   F_♮(x, S) = (F(x), DF(x)(S)),   J(x, S) = ‖∧_k(DF(x) ∘ S)‖,

    has the property [is_image_varifold]. The measure V⌞J (Federer 2.4.10)
    is a Radon measure because J is continuous and nonnegative (Federer
    4.1.14 support lemma [continuous_radon_density_radon]); its image under
    the continuous proper map F_♮ is a Radon measure by Federer 2.2.17; the
    integral formula follows from Federer 2.4.18 and 2.4.10. Allard obtains
    F_# V from the Borel set formula 3.2(1) directly; the existence proof
    here is the explicit image measure (see docs/divergences.md). This
    construction module is private: later files import
    AllardImageVarifold.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets functions reals
  constructive_ereal topology normedtype.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerNorm InnerMetric
  LinearBasis FiniteCoordinates Hom ExtendedRealOrderTopology PartialFunctionUP
  PartialFunctionPrecomposition PartialDensityProduct MeasureUP MeasureBasic MeasurePushforward
  RadonMeasureUP RadonBorelRegularity BorelRegularMeasureUP TopologicalBorel BorelFunctionUP
  BorelFunctionBasic ProperMapUP RadonProperPushforward MeasurableFunctionUP MeasureIntegralUP
  SummableRealFunctionUP MeasureStepIntegralIdentification PushforwardIntegral
  MeasureIntegralGraphEquivalence MeasurableGraphEquivalence MeasureDensityUP MeasureDensity
  MeasureChangeOfDensity ContinuousRadonDensity MetricClosedBalls EuclideanClosedBallCompact
  NormClassOneUP RealMetricBackground.
From Allard Require Import AllardGrassmann AllardVarifolds AllardImageVarifoldMaps AllardImageVarifoldUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section ImageVarifoldConstruction.
Variable R : realType.
Variables n k : nat.
Local Notation Rn := (R_n R n).
Local Notation hBn := (@euclidean_inner_productP R n).
Local Notation RnM := (inner_metric_space hBn).
Local Notation GA := (projection_grassmann R n k).
Local Notation GB := (grassmann_bundle R n k).

(** Source for [grassmann_bundle_closed_layer]: the compact sets
    {(x, S) : |x| ≤ j} = B(0, j) × G(n, k) exhausting G_k(R^n), used for
    Federer 2.2.5, pp. 62–63. Definition. *)
Definition grassmann_bundle_closed_layer (j : nat) : set GB :=
  [set z : GB | mdist (0 : RnM) z.1 <= j%:R].

(** Source for [grassmann_bundle_open_layer]: the open sets
    {(x, S) : |x| < j} of G_k(R^n), used for Federer 2.2.5, pp. 62–63.
    Definition. *)
Definition grassmann_bundle_open_layer (j : nat) : set GB :=
  [set z : GB | mdist (0 : RnM) z.1 < j%:R].

(** Source for [grassmann_bundle_closed_layer_compact]: B(0, j) × G(n, k)
    is compact, since closed balls of R^n and G(n, k) are compact.
    Supporting lemma. *)
Lemma grassmann_bundle_closed_layer_compact (j : nat) : compact (grassmann_bundle_closed_layer j).
Proof.
have h := @compact_setX RnM GA (metric_closed_ball (0 : RnM) j%:R) [set: GA]
  (@euclidean_closed_metric_ball_compact R n (0 : RnM) j%:R) (@projection_grassmann_compact R n k).
have -> : grassmann_bundle_closed_layer j =
    ((metric_closed_ball (0 : RnM) j%:R `*` [set: GA]) : set GB).
  by apply/seteqP; split=> z /=; [move=> h1; split|move=> []].
exact h.
Qed.

(** Source for [grassmann_bundle_open_layer_open]: {(x, S) : |x| < j} is
    open in G_k(R^n). Supporting lemma. *)
Lemma grassmann_bundle_open_layer_open (j : nat) : open (grassmann_bundle_open_layer j).
Proof.
have h := (proj1 (continuousP _) (@grassmann_bundle_point_continuous R n k))
  _ (@metric_open_ball_open R RnM (0 : RnM) j%:R).
exact h.
Qed.

(** Source for [grassmann_bundle_open_layer_cover]: every point of
    G_k(R^n) lies in some {(x, S) : |x| < j}. Supporting lemma. *)
Lemma grassmann_bundle_open_layer_cover : [set: GB] `<=` \bigcup_j grassmann_bundle_open_layer j.
Proof.
move=> z _; exists (Num.bound (mdist (0 : RnM) z.1)) => //.
exact: (archi_boundP (mdist_ge0 (0 : RnM) z.1)).
Qed.

(** Source for [jacobian_density_radon]: Federer 2.4.10, p. 85, and the
    support lemma for Federer 4.1.14, p. 371: if V ∈ V_k(R^n) and F is of
    class 1 with injective derivatives, then V⌞J is a Radon measure over
    G_k(R^n). Supporting lemma. *)
Lemma jacobian_density_radon (F : Rn -> Rn) (DF : Rn -> Hom Rn Rn) (V : set GB -> \bar R) :
  is_varifold V -> is_proper_class_one_immersion F DF ->
  is_varifold (measure_with_density V (real_total_integrand (image_bundle_jacobian DF))).
Proof.
move=> [hm hr] hF.
have hJc : continuous (image_bundle_jacobian DF : GB -> R^o).
  have h := @image_bundle_jacobian_continuous R n k F DF (immersion_class_one hF).
  exact h.
have hJ0 (z : GB) : 0 <= image_bundle_jacobian DF z.
  exact: ltW (image_bundle_jacobian_positive (immersion_injective hF) z).
split.
- have h := @measure_with_density_is_measure R GB V hm _
    (@continuous_radon_density_nonnegative R GB V hm (image_bundle_jacobian DF : GB -> R^o) hJ0).
  exact h.
- apply: (@continuous_radon_density_radon R GB V hm hr (image_bundle_jacobian DF : GB -> R^o) hJc hJ0
    _ _ grassmann_bundle_closed_layer_compact grassmann_bundle_open_layer_open).
  + move=> j z hz; exact: ltW.
  + move=> z hz; have [j _ hj] := grassmann_bundle_open_layer_cover hz.
    by exists j => //; exact: ltW.
  + exact: grassmann_bundle_open_layer_cover.
Qed.

(** Source for [image_varifold_witness]: Allard 3.2(1), p. 430: the
    measure F_♮ # (V⌞J) has the property of [is_image_varifold]. Radon by
    Federer 2.2.17 applied to the continuous proper map F_♮; the integral
    formula combines Federer 2.4.18 (image measures) and 2.4.10
    (densities). Supporting lemma. *)
Lemma image_varifold_witness (F : Rn -> Rn) (DF : Rn -> Hom Rn Rn) (V : set GB -> \bar R) :
  is_varifold V -> is_proper_class_one_immersion F DF ->
  is_image_varifold F DF V (measure_pushforward (image_bundle_map F DF)
    (measure_with_density V (real_total_integrand (image_bundle_jacobian DF)))).
Proof.
move=> hV hF; have [hm hr] := hV.
have hVJ := jacobian_density_radon hV hF.
have [hVJm hVJr] := hVJ.
have hFc := @image_bundle_map_continuous R n k F DF (immersion_class_one hF) (immersion_injective hF).
have hFp := @image_bundle_map_proper R n k F DF (immersion_class_one hF) (immersion_injective hF)
  (immersion_proper hF).
have hJc : continuous (image_bundle_jacobian DF : GB -> R^o).
  have h := @image_bundle_jacobian_continuous R n k F DF (immersion_class_one hF).
  exact h.
have hJ0 (z : GB) : 0 <= image_bundle_jacobian DF z.
  exact: ltW (image_bundle_jacobian_positive (immersion_injective hF) z).
split.
- exact: measure_pushforward_is_measure.
- exact: (proper_continuous_radon_pushforward hVJm hVJr (@metric_hausdorff R GB)
    (@grassmann_bundle_locally_compact R n k) hFc hFp).
- move=> alpha halpha a.
  pose Fn : GB -> GB := @image_bundle_map R n k F DF.
  pose J : GB -> R := @image_bundle_jacobian R n k DF.
  have hab : is_borel_function ((fun z : GB => alpha (Fn z)) : GB -> real_line_metric R).
    exact: (@borel_function_composition GB GB (real_line_metric R) Fn alpha
      (continuous_borel_function hFc) halpha).
  have hg1 x y : partial_function_graph (partial_function_precompose Fn (real_total_integrand alpha)) x y <->
      partial_function_graph (real_total_integrand (fun z : GB => alpha (Fn z))) x y.
    by [].
  have hg2 x y : partial_function_graph
      (partial_density_product (real_total_integrand (fun z : GB => alpha (Fn z)))
        (real_total_integrand J)) x y <->
      partial_function_graph (real_total_integrand (fun z : GB => alpha (Fn z) * J z)) x y.
    rewrite partial_density_product_graph real_total_integrand_graph; split.
    + move=> [b [c [hb [hc <-]]]].
      move: hb hc; rewrite !real_total_integrand_graph => <- <-; by rewrite EFinM.
    + move=> <-; exists (alpha (Fn x))%:E, (J x)%:E.
      by rewrite !real_total_integrand_graph EFinM.
  have hm1 : is_measure_measurable_function
      (measure_with_density V (real_total_integrand J))
      (partial_function_precompose Fn (real_total_integrand alpha)).
    apply: (@measurable_function_graph_equivalent R GB _ _
      (real_total_integrand (fun z : GB => alpha (Fn z)))).
    + by move=> x y; split=> h; apply/hg1.
    + exact: (varifold_borel_measurable hVJ hab).
  have hm2 : is_measure_measurable_function V (real_total_integrand (fun z : GB => alpha (Fn z))) :=
    varifold_borel_measurable hV hab.
  have hd := measure_density_integral_iff hm (measure_with_density_laws V (real_total_integrand J))
    (@continuous_radon_density_measurable R GB V hm hr (image_bundle_jacobian DF : GB -> R^o) hJc)
    (@continuous_radon_density_nonnegative R GB V hm (image_bundle_jacobian DF : GB -> R^o) hJ0)
    hm2 a.
  rewrite -(measure_pushforward_integral_iff hVJm hm1 a); split=> h.
  + have h1 := measure_integral_graph_equivalent hg1 h.
    have h2 := proj1 hd h1.
    exact: (measure_integral_graph_equivalent hg2 h2).
  + have h2 : is_measure_integral V (partial_density_product
        (real_total_integrand (fun z : GB => alpha (Fn z))) (real_total_integrand J)) a.
      by apply: (measure_integral_graph_equivalent _ h)=> x y; split=> hh; apply/hg2.
    have h1 := proj2 hd h2.
    by apply: (measure_integral_graph_equivalent _ h1)=> x y; split=> hh; apply/hg1.
Qed.

(** Source for [image_varifold_exists]: Allard 3.2, p. 430: there is a
    measure W which is F_# V whenever V ∈ V_k(R^n) and F satisfies the
    hypotheses of [is_proper_class_one_immersion]. Supporting lemma for
    the sealed choice. *)
Lemma image_varifold_exists (F : Rn -> Rn) (DF : Rn -> Hom Rn Rn) (V : set GB -> \bar R) :
  exists W : set GB -> \bar R,
    is_varifold V -> is_proper_class_one_immersion F DF -> is_image_varifold F DF V W.
Proof.
exists (measure_pushforward (image_bundle_map F DF)
  (measure_with_density V (real_total_integrand (image_bundle_jacobian DF)))).
exact: image_varifold_witness.
Qed.
End ImageVarifoldConstruction.
