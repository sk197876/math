(** Federer (1969), 2.4.12, pp. 87–88: sigma maps L1 into Y**, with
    sigma(f)(alpha) = integral alpha(f), and has norm at most phi_1(f). The
    existence proof was organised sequentially in
    MeasureVectorIntegralConstruction.v, using finite-image density and
    closedness of the scalar-evaluation specification. Here sigma is
    packaged afterwards as tau composed with that proved integral. Original
    partial domains are retained; addition uses common domains, consistently
    with the erratum, p. 2, book p. 87 lines 1 and 32. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import Hom RealNormUP NormMetric CompleteMetricUP PartialFunctionUP
  PartialNormedArithmetic MeasureUP MeasureIntegralUP MeasureLpMembershipUP MeasureLpNorm MeasureLpConvergence
  MeasureVectorIntegralUP MeasureVectorIntegral MeasureVectorIntegralBound
  MeasureVectorIntegralAddition MeasureVectorIntegralScale MeasureVectorIntegralDifference
  ContinuousDualUP ContinuousDualNorm ContinuousBidualUP ContinuousBidualSealed ContinuousBidualIsometry.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.
Section BidualIntegral.
Variable R : realType.
Variable X : choiceType.
Variables V D B : lmodType R.
Variable N : V -> R.
Hypothesis hN : is_real_norm N.
Hypothesis hY : is_complete_metric_space [the metricType R of real_norm_metric_space hN].
Variable mu : set X -> \bar R.
Hypothesis hm : is_measure mu.
Variable ed : Hom D (Hom V R^o).
Variable DN : D -> R.
Hypothesis hD : is_continuous_dual hN ed DN.
Variable eb : Hom B (Hom D R^o).
Variable BN : B -> R.
Hypothesis hB : is_continuous_dual (continuous_dual_norm_is_norm hD) eb BN.
Local Notation integral := (@measure_vector_integral R X V N hN hY mu hm).
Local Notation tau := (ContinuousBidual.value hB).

(** Source for [measure_bidual_integral]: sigma in Federer
    2.4.12, p. 87, represented through the already proved integral.
    Its dual-evaluation characterisation is proved immediately below. *)
Definition measure_bidual_integral (f : partial_function X (real_norm_metric_space hN))
    (hf : is_measure_lp_function mu 1%R f) : B := tau (integral hf).

(** Source for [measure_bidual_integral_evaluation]: the defining
    scalar-integral display for sigma, Federer 2.4.12, p. 87. *)
Lemma measure_bidual_integral_evaluation f hf (a : D) :
  is_measure_integral mu (partial_functional_evaluation f (hom_as_linear (ed a)))
    (eb (@measure_bidual_integral f hf) a)%:E.
Proof.
rewrite /measure_bidual_integral (ContinuousBidual.laws hB).
have hi := @measure_vector_integral_specification R X V N hN hY mu hm f hf.
exact (hi.2 (hom_as_linear (ed a)) (continuous_dual_continuous hD (a:=a))).
Qed.

(** Source for [measure_bidual_integral_bound]: |sigma(f)| <= phi_1(f),
    Federer 2.4.12, p. 87 *)
Lemma measure_bidual_integral_bound f hf :
  (BN (@measure_bidual_integral f hf))%:E <= measure_lp_norm mu N 1%R f.
Proof.
rewrite /measure_bidual_integral (continuous_bidual_isometry hB (ContinuousBidual.laws hB)).
exact: (@measure_vector_integral_norm_bound R X V N hN mu hm f _
  (measure_vector_integral_specification hY hm hf)).
Qed.

(** Source for [measure_bidual_integral_add]: linearity of sigma
    under addition on common partial domains, Federer 2.4.12, p. 87. *)
Lemma measure_bidual_integral_add f g hf hg hfg :
  @measure_bidual_integral (partial_vector_add f g) hfg =
  (@measure_bidual_integral f hf + @measure_bidual_integral g hg)%R.
Proof.
have he : integral hfg = (integral hf + integral hg)%R.
  apply: measure_vector_integral_unique (measure_vector_integral_specification hY hm hfg) _.
  exact: (@measure_vector_integral_add R X V N hN mu hm f g _ _
    (measure_vector_integral_specification hY hm hf) (measure_vector_integral_specification hY hm hg)).
by rewrite /measure_bidual_integral he linearD.
Qed.

(** Source for [measure_bidual_integral_scale]: scalar linearity
    of sigma, including scalar zero, Federer 2.4.12, p. 87. *)
Lemma measure_bidual_integral_scale f hf c hcf :
  @measure_bidual_integral (partial_vector_scale c f) hcf =
  (c *: @measure_bidual_integral f hf)%R.
Proof.
have he : integral hcf = (c *: integral hf)%R.
  apply: measure_vector_integral_unique (measure_vector_integral_specification hY hm hcf) _.
  exact: (@measure_vector_integral_scale R X V N hN mu hm c f _
    (measure_vector_integral_specification hY hm hf)).
by rewrite /measure_bidual_integral he linearZ.
Qed.

(** Source for [measure_bidual_integral_distance_bound]: continuity
    of sigma in the L1 seminorm, Federer 2.4.12, p. 87, expressed
    as its stronger Lipschitz estimate on original partial-domain inputs. *)
Lemma measure_bidual_integral_distance_bound f g hf hg :
  (BN (@measure_bidual_integral f hf - @measure_bidual_integral g hg)%R)%:E <=
    measure_lp_distance mu N 1%R f g.
Proof.
rewrite /measure_bidual_integral -linearB
  (continuous_bidual_isometry hB (ContinuousBidual.laws hB)).
exact: (@measure_vector_integral_distance_bound R X V N hN mu hm f g _ _
  (measure_vector_integral_specification hY hm hf) (measure_vector_integral_specification hY hm hg)).
Qed.

(** Source for [measure_bidual_integral_in_image]: sigma inverse
    of im(tau) is all of L1, Federer 2.4.12, p. 88, first display.
    In the sequential proof order this is a consequence of the proved
    representation theorem, rather than a new existence premise. *)
Lemma measure_bidual_integral_in_image f hf :
  exists y : V, tau y = @measure_bidual_integral f hf.
Proof. by exists (integral hf). Qed.
End BidualIntegral.
