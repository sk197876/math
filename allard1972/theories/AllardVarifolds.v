(** Allard (1972), 3.1, printed p. 429; blueprint labels al:3.1 and
    al:3.1:lem, specialised to M = U = R^n. A k dimensional varifold in
    R^n is a Radon measure V over G_k(R^n) = R^n × G(n, k)
    ([is_varifold]); the space of such varifolds is V_k(R^n). The
    weight of V is the image measure ‖V‖ = π_# V under the projection
    π(x, S) = x ([varifold_weight]), that is

        ‖V‖(A) = V(G_k(R^n) ∩ {(x, S) : x ∈ A})   for A ⊆ R^n,

    and ‖V‖ is a Radon measure over R^n ([allard_3_1]), because π is
    continuous and proper (Federer 2.2.17). Integration with respect to
    ‖V‖ is integration of f(x) with respect to V(x, S) (Federer 2.4.18;
    [allard_3_1_weight_integral], [allard_3_1_weight_borel_integral]).
    The weak topology on V_k(R^n) is not used on the Michael–Simon path
    and is not formalised. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets functions reals
  constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerNorm InnerMetric
  LinearBasis FiniteCoordinates AffineGroupTopology TopologicalProductMaps MetricProductBackground
  ExtendedRealOrderTopology PartialFunctionUP PartialFunctionPrecomposition MeasureUP MeasurePushforward RadonMeasureUP
  RadonBorelRegularity BorelRegularMeasureUP TopologicalBorel BorelFunctionUP BorelFunctionBasic
  ProperMapUP RadonProperPushforward MeasurableFunctionUP MeasureIntegralUP SummableRealFunctionUP
  MeasureStepIntegralIdentification PushforwardIntegral MeasureIntegralGraphEquivalence
  BVCurveMeasurable MeasurableGraphEquivalence RealMetricBackground.
From Allard Require Import AllardGrassmann.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section Varifolds.
Variable R : realType.
Variables n k : nat.
Local Notation hBn := (@euclidean_inner_productP R n).
Local Notation hbn := (@coordinate_basisP R n).
Local Notation RnM := (inner_metric_space hBn).
Local Notation GA := (projection_grassmann R n k).
Local Notation GB := (grassmann_bundle R n k).

(** Source for [is_varifold]: Allard 3.1, p. 429: "We say V is a k
    dimensional varifold in M if V is a Radon measure on G_k(M)", for
    M = R^n; blueprint al:3.1. A measure over G_k(R^n) in the sense of
    Federer 2.1.2 which is a Radon measure in the sense of Federer 2.2.5;
    by the blueprint remark rem:2.6(2) these are Allard's Radon measures
    of 2.6(2). Definition. *)
Record is_varifold (V : set GB -> \bar R) : Prop := {
  (** Source for [varifold_measure]: Allard 3.1, p. 429: V is a measure
      over G_k(R^n), Federer 2.1.2. *)
  varifold_measure : is_measure V;
  (** Source for [varifold_radon]: Allard 3.1, p. 429: V is a Radon
      measure, Federer 2.2.5. *)
  varifold_radon : is_radon_measure V
}.

(** Source for [grassmann_bundle_point]: Allard 3.1, p. 429: the
    projection π : G_k(R^n) → R^n, π(x, S) = x, of blueprint
    al:3.1:lem. Definition. *)
Definition grassmann_bundle_point (z : GB) : RnM := z.1.

(** Source for [varifold_weight]: Allard 3.1, p. 429: the weight
    ‖V‖(A) = V(G_k(R^n) ∩ {(x, S) : x ∈ A}) for A ⊆ R^n, that is
    ‖V‖ = π_# V (Federer 2.1.2); blueprint al:3.1. Definition. *)
Definition varifold_weight (V : set GB -> \bar R) : set RnM -> \bar R :=
  measure_pushforward grassmann_bundle_point V.

(** Source for [varifold_weightE]: Allard 3.1, p. 429, the display
    ‖V‖(A) = V(G_k(R^n) ∩ {(x, S) : x ∈ A}). Supporting lemma. *)
Lemma varifold_weightE (V : set GB -> \bar R) (A : set RnM) :
  varifold_weight V A = V [set z : GB | A z.1].
Proof. by []. Qed.

(** Source for [grassmann_bundle_point_continuous]: blueprint
    al:3.1:lem: π is continuous. Supporting lemma. *)
Lemma grassmann_bundle_point_continuous : continuous grassmann_bundle_point.
Proof. exact: (@first_projection_continuous RnM GA). Qed.

(** Source for [grassmann_bundle_point_preimage]: blueprint al:3.1:lem:
    π^{-1}[K] = K × G(n, k). Supporting lemma. *)
Lemma grassmann_bundle_point_preimage (K : set RnM) :
  grassmann_bundle_point @^-1` K = (K `*` [set: GA] : set GB).
Proof. by apply/seteqP; split=> z /=; [move=> h; split|move=> []]. Qed.

(** Source for [grassmann_bundle_point_proper]: blueprint al:3.1:lem:
    "π^{-1}[K] ⊆ K × G(n, k) is compact for compact K", since G(n, k)
    is compact (new:grass_compact). Supporting lemma. *)
Lemma grassmann_bundle_point_proper : is_proper_map grassmann_bundle_point.
Proof.
move=> K hK; rewrite grassmann_bundle_point_preimage.
have h := @compact_setX RnM GA K [set: GA] hK (@projection_grassmann_compact R n k).
exact h.
Qed.

(** Source for [euclidean_metric_hausdorff]: R^n is a Hausdorff space.
    Supporting lemma. *)
Lemma euclidean_metric_hausdorff : hausdorff_space RnM.
Proof. exact: (@metric_hausdorff R RnM). Qed.

(** Source for [euclidean_metric_locally_compact]: R^n is locally
    compact. Supporting lemma. *)
Lemma euclidean_metric_locally_compact : locally_compact [set: RnM].
Proof. exact: (@inner_space_locally_compact R (R_n R n) _ hBn n _ hbn). Qed.

(** Source for [allard_3_1]: Allard 3.1, p. 430: "Clearly, ‖V‖ is a
    Radon measure on M"; blueprint al:3.1:lem, for M = R^n. The proof
    applies Federer 2.2.17 to the continuous proper map π. *)
Theorem allard_3_1 (V : set GB -> \bar R) :
  is_varifold V -> is_measure (varifold_weight V) /\ is_radon_measure (varifold_weight V).
Proof.
move=> [hm hr]; split; first exact: measure_pushforward_is_measure.
exact: (@proper_continuous_radon_pushforward R GB RnM V hm hr grassmann_bundle_point
  euclidean_metric_hausdorff euclidean_metric_locally_compact
  grassmann_bundle_point_continuous grassmann_bundle_point_proper).
Qed.

(** Source for [allard_3_1_weight_integral]: Allard 3.1, p. 429, the
    weight as an image measure, with Federer 2.4.18, pp. 90–91:
    ∫ f d‖V‖ = ∫ f(x) dV(x, S), as an equivalence of integral values,
    whenever [(x, S) ↦ f(x)] is V measurable. Direct formalisation. *)
Theorem allard_3_1_weight_integral (V : set GB -> \bar R)
    (f : partial_function RnM (extended_real_line R)) :
  is_varifold V ->
  is_measure_measurable_function V (partial_function_precompose grassmann_bundle_point f) ->
  forall a, is_measure_integral (varifold_weight V) f a <->
    is_measure_integral V (partial_function_precompose grassmann_bundle_point f) a.
Proof.
move=> [hm _] hf a; split=> h.
- exact/(measure_pushforward_integral_iff hm hf).
- exact/(measure_pushforward_integral_iff hm hf).
Qed.

(** Source for [varifold_borel_measurable]: a real valued Borel
    function on G_k(R^n) is V measurable for every varifold V, since V
    is Borel regular (Federer 2.2.5, 2.3.2). Supporting lemma. *)
Lemma varifold_borel_measurable (V : set GB -> \bar R) (g : GB -> R) :
  is_varifold V -> is_borel_function (g : GB -> real_line_metric R) ->
  is_measure_measurable_function V (real_total_integrand g).
Proof.
move=> [hm hr] hg.
apply: (@measurable_partial_real_embedding R GB V hm).
exact: (@borel_map_measure_measurable R GB (real_line_metric R) V g hm
  (radon_borel_regular hm hr) hg).
Qed.

(** Source for [allard_3_1_weight_borel_integral]: Allard 3.1, p. 429,
    with Federer 2.4.18, pp. 90–91: for a real valued Borel function f
    on R^n, ∫ f d‖V‖ = ∫ f(x) dV(x, S), as an equivalence of integral
    values (either side may be infinite or undefined). Direct
    formalisation. *)
Theorem allard_3_1_weight_borel_integral (V : set GB -> \bar R) (f : RnM -> R) :
  is_varifold V -> is_borel_function (f : RnM -> real_line_metric R) ->
  forall a, is_measure_integral (varifold_weight V) (real_total_integrand f) a <->
    is_measure_integral V (real_total_integrand (fun z : GB => f z.1)) a.
Proof.
move=> hV hf a.
have hfg : is_borel_function ((fun z : GB => f z.1) : GB -> real_line_metric R).
  exact: (@borel_function_composition GB RnM (real_line_metric R) grassmann_bundle_point f
    (continuous_borel_function grassmann_bundle_point_continuous) hf).
have hgraph x y : partial_function_graph
    (partial_function_precompose grassmann_bundle_point (real_total_integrand f)) x y <->
    partial_function_graph (real_total_integrand (fun z : GB => f z.1)) x y.
  by [].
have hmeas : is_measure_measurable_function V
    (partial_function_precompose grassmann_bundle_point (real_total_integrand f)).
  apply: (@measurable_function_graph_equivalent R GB _ V
    (real_total_integrand (fun z : GB => f z.1))).
  - by move=> x y; split=> h; apply/hgraph.
  - exact: varifold_borel_measurable.
rewrite (allard_3_1_weight_integral hV hmeas a); split=> h.
- exact: (measure_integral_graph_equivalent hgraph h).
- by apply: (measure_integral_graph_equivalent _ h)=> x y; split=> hh; apply/hgraph.
Qed.

End Varifolds.

