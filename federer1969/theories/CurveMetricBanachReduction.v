(** Federer (1969), 2.5.16, p. 110: "The assumption that Y be a Banach space
    is not as restrictive as it may seem, because for any metric space Y we
    can consider the Banach space E of all bounded real valued continuous
    functions on Y with the norm nu(f) = sup im |f| whenever f in E, choose
    any base point eta in Y, and construct the isometric embedding F : Y ->
    E, F(y)(w) = rho(y, w) - rho(eta, w) for y, w in Y." Here F is specified
    by its values; existence follows from the surjectivity of the evaluation
    of E onto the bounded continuous functions, and
    MetricBoundedContinuousEmbedding.v shows that the prescribed functions
    are bounded and continuous. The isometry is proved as an identity of
    distances in the metric of nu. Consequently F o g has the same chain
    sums, variation and arc length function s as g, and the Banach extension
    H of 2.5.16, p. 110, exists for F o g, with H o s = F o g; no
    completeness of Y is required for this. The local erratum has no entry
    for p. 110. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals
  constructive_ereal topology normedtype.
From Federer Require Import RealNormUP NormMetric CompleteMetricUP MetricBoundedContinuousEmbedding
  UniformFunctionNormUP BoundedContinuousSpaceUP BoundedContinuousSpaceLaws BoundedContinuousBanachSpace
  ExtendedRealBoundsUP ExtendedRealBounds
  CurveVariationUP CurveArcLength CurveBanachExtension.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section MetricBanachReduction.
Variable R : realType.
Variable Y : metricType R.
Variable eta : Y.
Local Notation E := (real_norm_metric_space (@bounded_continuous_space_norm_laws R Y)).
Local Notation ev := (@bounded_continuous_evaluate R Y).
Local Notation N := (@bounded_continuous_space_norm R Y).
(** Source for [hv]: the abstract laws of the Banach space E of
    Federer 2.5.16, p. 110, from BoundedContinuousBanachSpace.v. *)
Let hv := @bounded_continuous_space_specification R Y.

(** Source for [is_metric_banach_embedding]: the map F : Y -> E of
    Federer 2.5.16, p. 110, specified by
    F(y)(w) = rho(y, w) - rho(eta, w) for y, w in Y. *)
Definition is_metric_banach_embedding (F : Y -> E) : Prop :=
  forall y, ev (F y) = metric_embedding eta y.

(** Source for [metric_banach_embedding_exists]: the map F of Federer
    2.5.16, p. 110, exists: each F(y) is a bounded continuous
    real function on Y, hence a member of E. *)
Lemma metric_banach_embedding_exists : exists F : Y -> E, is_metric_banach_embedding F.
Proof.
have h : forall y, exists v : E, ev v = metric_embedding eta y.
  move=> y; exact: (bounded_continuous_evaluation_surjective hv (metric_embedding_member eta y)).
have [f hf] := choice h.
by exists f.
Qed.

Variable F : Y -> E.
Hypothesis hF : is_metric_banach_embedding F.

(** Source for [metric_banach_embedding_isometric]: F is an isometric
    embedding, Federer 2.5.16, p. 110: nu(F(y) - F(y')) = rho(y, y'),
    so the distance of F(y) and F(y') in E equals rho(y, y'). *)
Theorem metric_banach_embedding_isometric (y y' : Y) : mdist (F y) (F y') = mdist y y'.
Proof.
rewrite real_norm_metric_distanceE.
have hn := bounded_continuous_norm_supremum hv (F y - F y').
rewrite (bounded_continuous_evaluation_subtract hv) !hF in hn.
apply: (uniform_function_norm_unique hn); constructor.
- exact: mdist_ge0.
- move=> w; exact: metric_embedding_distance_le.
- move=> c _ hc; rewrite -(metric_embedding_distance_attained eta y y'); exact: hc y'.
Qed.

Variable g : R -> Y.

(** Source for [chain_sum_metric_banach_embedding]: the sums
    sum_i rho[g(t_i), g(t_(i+1))] of Federer 2.5.16, p. 109, are
    unchanged when g is replaced by F o g, F being isometric (p. 110). *)
Lemma chain_sum_metric_banach_embedding (s : seq R) : chain_sum (F \o g) s = chain_sum g s.
Proof.
elim: s=> [//|t s ih]; case: s ih=> [//|u s] ih.
by rewrite !chain_sum_cons ih /= metric_banach_embedding_isometric.
Qed.

(** Source for [curve_variation_metric_banach_embedding]: F o g has the
    same variation V_a^b as g, Federer 2.5.16, pp. 109–110. *)
Theorem curve_variation_metric_banach_embedding (a b : R) :
  curve_variation (F \o g) a b = curve_variation g a b.
Proof.
rewrite /curve_variation; congr extended_real_sup.
apply/seteqP; split=> v [s [hs ->]]; exists s; split=> //.
- by rewrite chain_sum_metric_banach_embedding.
- by rewrite chain_sum_metric_banach_embedding.
Qed.

(** Source for [curve_locally_finite_metric_banach_embedding]: the
    hypothesis V_a^b g < oo whenever -oo < a < b < oo of Federer
    2.5.16, p. 109, holds for F o g if and only if it holds for g. *)
Lemma curve_locally_finite_metric_banach_embedding :
  curve_locally_finite_variation (F \o g) <-> curve_locally_finite_variation g.
Proof.
by split=> h a b hab; [rewrite -curve_variation_metric_banach_embedding | rewrite curve_variation_metric_banach_embedding]; exact: h.
Qed.

(** Source for [arc_length_metric_banach_embedding]: F o g and g have
    the same function s(x) = V_0^x of Federer 2.5.16, p. 109. *)
Lemma arc_length_metric_banach_embedding : arc_length (F \o g) = arc_length g.
Proof. by apply: funext=> x; rewrite /arc_length !curve_variation_metric_banach_embedding. Qed.

(** Source for [curve_metric_banach_reduction]: the reduction stated in
    Federer 2.5.16, p. 110: for any metric space Y and any g : R -> Y
    with V_a^b g < oo whenever -oo < a < b < oo, the Banach extension
    H : R -> E of 2.5.16 exists for F o g, where E is the Banach space of
    bounded continuous real functions on Y and F the isometric embedding;
    moreover H(s(t)) = F(g(t)) with s the arc length function of g
    itself. No completeness of Y is assumed. *)
Theorem curve_metric_banach_reduction :
  curve_locally_finite_variation g ->
  exists H : R -> E,
    @is_curve_banach_extension R _ _ (@bounded_continuous_space_norm_laws R Y) (F \o g) H /\
    forall t, H (arc_length g t) = F (g t).
Proof.
move=> hfin.
have hfin' : curve_locally_finite_variation (F \o g).
  exact: (proj2 curve_locally_finite_metric_banach_embedding hfin).
have [H hH] := @curve_banach_extension_exists R _ _ (@bounded_continuous_space_norm_laws R Y)
  (@bounded_continuous_space_banach R Y) (F \o g) hfin'.
exists H; split=> // t.
by rewrite -arc_length_metric_banach_embedding (curve_banach_compose hH).
Qed.

End MetricBanachReduction.
