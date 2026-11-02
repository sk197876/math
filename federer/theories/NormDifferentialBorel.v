(** Federer (1969), 3.1.1, p. 211: for a class-zero function
    with finite-dimensional source and complete target, domain Df
    is Borel and Df is Borel measurable in the operator norm.
    The proof follows the printed closed separable target reduction,
    countable remainder graph formula, and injective projection. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets cardinality reals topology.
From Federer Require Import Hom ModuleQuotient SubspaceCarrier RealNormUP NormMetric LinearBasis
  NormedSubspace SubspaceNormSeparability ClosedNormSubspaceCompleteness ClosedLinearSpanUP
  NormDifferentialUP NormDifferential NormDifferentialClosedRange NormClassOneUP
  NormBoundedLinearTopology CompleteMetricUP ContinuousOperatorUP ContinuousOperatorSealed
  ContinuousOperatorNorm ContinuousOperatorCompleteness ContinuousOperatorSeparability
  ContinuousOperatorSubspaceInclusion NormContinuousSeparableRange
  NormDifferentialBorelParameter TopologicalBorel PartialFunctionUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section DifferentialBorel.
Variable R : realType.
Variables X Y Z : lmodType R.
Variable NX : X -> R.
Variable NY : Y -> R.
Hypothesis hNX : is_real_norm NX.
Hypothesis hNY : is_real_norm NY.
Variable evaluation : Hom Z (Hom X Y).
Variable ZN : Z -> R.
Hypothesis hZ : is_continuous_operator_space NX NY evaluation ZN.
Variable n : nat.
Variable e : 'I_n -> X.
Hypothesis he : is_basis e.
Variable A : set X.
Variable f : X -> Y.
Hypothesis hf : norm_class_zero NX NY A f.
Hypothesis hY : is_complete_metric_space (real_norm_metric_space hNY).
Let E := real_norm_metric_space hNX.
Let T := real_norm_metric_space (continuous_operator_norm_is_norm hNY hZ).

(** Source for [norm_differential_borel_values]: the Borel
    inverse-image assertion for Df in 3.1.1, p. 211, for every
    Borel subset of the normed operator space. The original
    complete target need not be separable or finite dimensional. *)
Theorem norm_differential_borel_values (B : set T) :
  borel_set B -> @borel_set [the topologicalType of E]
    [set a | exists z, has_norm_differential NX NY A f a (evaluation z) /\ B z].
Proof.
move=> hB.
have [S [hc [hr hs]]] := @norm_class_zero_separable_linear_range
  R X Y NX NY hNX hNY n e he A f hf.
pose Y0 := [the lmodType R of subspace_space S].
pose N0 := subspace_norm NY S.
pose hN0 := subspace_norm_laws hNY S.
pose Z0 := @ContinuousOperator.space R X Y0 NX N0 hNX hN0.
pose ev0 := @ContinuousOperator.evaluation R X Y0 NX N0 hNX hN0.
pose ZN0 := @ContinuousOperator.norm R X Y0 NX N0 hNX hN0.
have hZ0 : is_continuous_operator_space NX N0 ev0 ZN0 :=
  @ContinuousOperator.laws R X Y0 NX N0 hNX hN0.
pose hZN0 := continuous_operator_norm_is_norm hN0 hZ0.
pose W := [the metricType R of real_norm_metric_space hZN0].
have hY0 : is_complete_metric_space (real_norm_metric_space hN0).
  exact: closed_norm_subspace_complete hY hc.
have hsY0 := subspace_norm_separable hs.
have hW : is_complete_metric_space W :=
  @continuous_operator_complete R X Y0 Z0 NX N0 hNX hN0 ev0 ZN0 hZ0 n e he hY0.
have hsW : exists D : set W, countable D /\ dense D :=
  @continuous_operator_separable R X Y0 Z0 NX N0 hNX hN0 ev0 ZN0 hZ0 n e he hsY0.
have [j hj] := @continuous_operator_subspace_inclusion_exists
  R X Y Z NX NY S Z0 evaluation ZN hZ ev0 ZN0 hZ0.
have hjnorm z : ZN (j z)=ZN0 z :=
  @continuous_operator_subspace_inclusion_isometry R X Y Z NX NY S Z0
    evaluation ZN hZ ev0 ZN0 hZ0 j hj z.
have hjinj : injective j := @continuous_operator_subspace_inclusion_injective
  R X Y Z NX NY S Z0 evaluation ev0 ZN0 hZ0 j hj.
have hjcont : continuous (fun w : W => (j w : T)).
  apply: (@norm_bounded_linear_continuous R Z0 Z ZN0 ZN hZN0
    (continuous_operator_norm_is_norm hNY hZ) j).
  exists 1; split; first exact: ler01.
  move=> z; by rewrite hjnorm mul1r.
have hcover a L : has_norm_differential NX NY A f a L -> exists w : W, evaluation (j w)=L.
  move=> hD.
  apply: (@continuous_operator_subspace_inclusion_represents R X Y Z NX NY S Z0
    evaluation ev0 ZN0 hZ0 j hj L (norm_differential_bounded hD)).
  apply: (@norm_differential_closed_linear_range R X Y NX NY hNX hNY A f a L S hc _ hD).
  move=> x hx; apply: hr; by exists x.
exact: (@norm_differential_borel_parameter_preimage R X Y Z NX NY hNX hNY
  evaluation ZN hZ n e he A f W (fun w : W => (j w : T))
  hf hW hsW hjcont hjinj hcover B hB).
Qed.

(** Source for [norm_differential_domain_borel]: domain Df is
    Borel, Federer 3.1.1, p. 211. This refers to the exact
    sealed differential graph introduced on p. 209. *)
Theorem norm_differential_domain_borel :
  @borel_set [the topologicalType of E]
    (partial_function_domain (norm_differential hNX hNY A f)).
Proof.
have hb := norm_differential_borel_values (open_borel_set (@openT T)).
have heq : partial_function_domain (norm_differential hNX hNY A f)=
    [set a : E | exists z, has_norm_differential NX NY A f a (evaluation z) /\ setT z].
  apply/seteqP; split=> a.
  - move=> [L hL]; have hD := (norm_differential_graph hNX hNY A f a L).1 hL.
    have [z hz] := continuous_operator_surjective hZ (norm_differential_bounded hD).
    exists z; split=> //; by rewrite hz.
  - move=> [z [hD _]]; exists (evaluation z).
    exact: (norm_differential_graph hNX hNY A f a (evaluation z)).2 hD.
by rewrite heq.
Qed.

(** Source for [norm_differential_borel_preimage]: Df is Borel
    measurable in the normed space of continuous linear maps,
    Federer 3.1.1, p. 211. Evaluation identifies abstract
    operators with their linear maps in the exact sealed graph;
    points outside domain Df belong to no inverse image. *)
Theorem norm_differential_borel_preimage (B : set T) :
  borel_set B -> @borel_set [the topologicalType of E]
    (partial_function_preimage (norm_differential hNX hNY A f) (evaluation @` B)).
Proof.
move=> hB; have hb := norm_differential_borel_values hB.
have heq : partial_function_preimage (norm_differential hNX hNY A f) (evaluation @` B)=
    [set a : E | exists z, has_norm_differential NX NY A f a (evaluation z) /\ B z].
  apply/seteqP; split=> a.
  - move=> [L [hL [z hz hez]]]; exists z; split=> //.
    apply: (norm_differential_graph hNX hNY A f a (evaluation z)).1.
    by rewrite hez.
  - move=> [z [hD hz]]; exists (evaluation z); split; last by exists z.
    exact: (norm_differential_graph hNX hNY A f a (evaluation z)).2 hD.
by rewrite heq.
Qed.
End DifferentialBorel.
