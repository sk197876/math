(** Federer (1969), 3.2.2, p. 242: closed tests for the
    differential's vector bounds and the uniform finite-radius
    remainder. Arbitrary intersections are permitted here because
    all fixed-increment tests are closed. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormMetric NormMetricContinuity
  NormDifferentialUP NormClassOneUP ContinuousOperatorUP ContinuousOperatorNorm
  ContinuousOperatorEvaluation NormDifferentialRemainderOpen MetricProductBackground
  TopologicalProductMaps CountableOrderIntervals RealMetricBackground.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory numFieldTopology.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section ModelTests.
Variable R:realType.
Variables X Y Z:lmodType R.
Variables NX:X->R.
Variable NY:Y->R.
Hypothesis hNX:is_real_norm NX.
Hypothesis hNY:is_real_norm NY.
Variable ev:Hom Z (Hom X Y).
Variable ZN:Z->R.
Hypothesis hZ:is_continuous_operator_space NX NY ev ZN.
Let E:=real_norm_metric_space hNX.
Let T:=real_norm_metric_space (continuous_operator_norm_is_norm hNY hZ).
Let P:=metric_product E T.
Variable s:Hom X X.
Variables a b:R.
Variable f:X->Y.
Variables e r:R.

(** Source for [linear_model_vector_test]: the first condition
    defining Z(s,i), Federer 3.2.2, p. 242, applied to
    a candidate actual differential represented by z. *)
Definition linear_model_vector_test:set T:=
  [set z|forall v,a*NX (s v)<=NY (ev z v) /\ NY (ev z v)<=b*NX (s v)].

(** Source for [linear_model_vector_test_closed]: the Borel
    assertion for Z(s,i) in Federer 3.2.2, p. 242.
    Fixed-vector operator evaluations and norms are continuous;
    both non-strict inequalities therefore define closed sets. *)
Lemma linear_model_vector_test_closed:closed linear_model_vector_test.
Proof.
have he:linear_model_vector_test=\bigcap_v
    ([set z:T|a*NX (s v)<=NY (ev z v)] `&`
     [set z:T|NY (ev z v)<=b*NX (s v)]).
  apply/seteqP; split=>z hz.
  - by move=>v _; exact (hz v).
  - move=>v; exact (hz v Logic.I).
rewrite he; apply:closed_bigI=>v _; apply:closedI.
- have hc:continuous (fun z:T=>(NY (ev z v):real_line_metric R)).
    move=>z; exact (continuous_comp (@continuous_operator_evaluation_continuous R X Y Z NX NY hNX hNY ev ZN hZ v z)
      (@real_norm_metric_norm_continuous R Y NY hNY (ev z v))).
  exact ((@continuous_closedP T (real_line_metric R) _).1 hc _
    (@order_closed_upper_ray_closed _ [the orderTopologicalType _ of R^o] (a*NX (s v)))).
- have hc:continuous (fun z:T=>(NY (ev z v):real_line_metric R)).
    move=>z; exact (continuous_comp (@continuous_operator_evaluation_continuous R X Y Z NX NY hNX hNY ev ZN hZ v z)
      (@real_norm_metric_norm_continuous R Y NY hNY (ev z v))).
  exact ((@continuous_closedP T (real_line_metric R) _).1 hc _
    (@order_closed_lower_ray_closed _ [the orderTopologicalType _ of R^o] (b*NX (s v)))).
Qed.

(** Source for [linear_model_remainder_test]: the second
    condition defining Z(s,i), Federer 3.2.2, p. 242.
    The closed ball is retained, including its boundary. *)
Definition linear_model_remainder_test:set P:=
  [set p|forall h,NX h<=r -> NY (f (p.1+h)-f p.1-ev p.2 h)<=e*NX (s h)].

(** Source for [linear_model_remainder_test_closed]: the Borel
    assertion for Z(s,i), Federer 3.2.2, p. 242.
    Continuity of f on the entire source makes each strict
    remainder violation open in point times operator. *)
Lemma linear_model_remainder_test_closed:
  norm_class_zero NX NY setT f -> closed linear_model_remainder_test.
Proof.
move=>hf.
pose U:set P:=\bigcup_(h in [set h:X|NX h<=r])
  [set p:P|setT p.1 /\ setT (p.1+h) /\ e*NX (s h)<NY (f (p.1+h)-f p.1-ev p.2 h)].
have hU:open U.
  apply:bigcup_open=>h hh.
  exact (@norm_differential_remainder_violation_open R X Y Z NX NY hNX hNY ev ZN hZ
    setT f h (e*NX (s h)) hf).
have he:linear_model_remainder_test=~` U.
  apply/seteqP; split=>p.
  - move=>hp [h hh [_ [_ hbad]]].
    by have:=lt_le_trans hbad (hp h hh); rewrite ltxx.
  - move=>hp h hh.
    case: (leP (NY (f (p.1+h)-f p.1-ev p.2 h)) (e*NX (s h)))=>hbad; first by [].
    exfalso; apply:hp.
    exists h=>//; by split; last split.
by rewrite he closedC.
Qed.

(** Source for [linear_model_combined_test_closed]: the two
    conditions in Z(s,i), Federer 3.2.2, p. 242, are
    closed together before restricting to the actual Borel
    differential graph. No Borel derivative is assumed. *)
Lemma linear_model_combined_test_closed:
  norm_class_zero NX NY setT f ->
  closed [set p:P|linear_model_vector_test p.2 /\ linear_model_remainder_test p].
Proof.
move=>hf; apply:closedI; last exact:linear_model_remainder_test_closed.
exact ((@continuous_closedP P T (@snd E T)).1 (@second_projection_continuous E T) _
  linear_model_vector_test_closed).
Qed.
End ModelTests.
