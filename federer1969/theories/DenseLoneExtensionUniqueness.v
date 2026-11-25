(** Federer (1969), 4.1.5, p. 350:
    the continuous extension is uniquely determined
    because actual tests are L1 dense. This
    argument is stated for an arbitrary family
    of original partial functions and retains
    seminorm-zero representatives. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology ring lra.
From Federer Require Import RealNormUP NormMetric PartialFunctionUP MeasureUP MeasureLpMembershipUP
  MeasureLpConvergence MeasureLpDistanceLaws LoneSeminormContinuityUP VectorDaniellDualExtension.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [dense_lone_extension_unique]: the exact
    density implication cited for uniqueness in
    Federer 4.1.5, p. 350. The reference
    extension may satisfy the sharper Lipschitz bound. *)
Theorem dense_lone_extension_unique (R:realType) (X:choiceType)
    (Y:lmodType R) (NY:Y->R) (hNY:is_real_norm NY)
    (mu:set X->\bar R) (hm:is_measure mu) (P:Type)
    (test:P->partial_function X (real_norm_metric_space hNY))
    (I J:partial_function X (real_norm_metric_space hNY)->R):
  (forall (f g:partial_function X (real_norm_metric_space hNY)),is_measure_lp_function mu 1 f ->is_measure_lp_function mu 1 g ->
    (`|I f-I g|%:E<=measure_lp_distance mu NY 1 f g)%E) ->
  @is_lone_seminorm_continuous R X Y NY hNY mu J ->
  (forall (f:partial_function X (real_norm_metric_space hNY)),is_measure_lp_function mu 1 f ->forall epsilon:R,0<epsilon ->
    exists p:P,is_measure_lp_function mu 1 (test p) /\
      (measure_lp_distance mu NY 1 f (test p)<epsilon%:E)%E) ->
  (forall p,I (test p)=J (test p)) ->
  forall (f:partial_function X (real_norm_metric_space hNY)),is_measure_lp_function mu 1 f ->I f=J f.
Proof.
move=>hLipschitz hContinuous hDense hAgreement f hf.
apply/eqP; rewrite -subr_eq0; apply/eqP.
apply:real_small_zero=>epsilon hEpsilon.
have hHalf:0<epsilon/2 by rewrite divr_gt0 // ltr0n.
have[delta [hDelta hJ]]:=@hContinuous f hf (epsilon/2) hHalf.
pose eta:=Num.min (epsilon/2) (delta/2).
have hEta:0<eta by rewrite /eta lt_min hHalf; rewrite divr_gt0 // ltr0n.
have[p [hp hDistance]]:=hDense f hf eta hEta.
have hILess:`|I f-I (test p)|<eta.
  have hBound:=hLipschitz f (test p) hf hp.
  have hStrict:=le_lt_trans hBound hDistance.
  by move:hStrict; rewrite lte_fin.
have hSymmetric:=@measure_lp_distance_symmetric R X Y NY hNY mu hm 1 f (test p)
  (lexx _) hf.2.1 hp.2.1.
have hDeltaLess:(measure_lp_distance mu NY 1 (test p) f<delta%:E)%E.
  rewrite -hSymmetric; apply:lt_le_trans hDistance _; rewrite lee_fin.
  have hEtaDelta:eta<=delta/2 by rewrite /eta ge_min lexx orbT.
  have hHalfDelta:delta/2<=delta by lra.
  exact:le_trans hEtaDelta hHalfDelta.
have hJLess:=hJ (test p) hp hDeltaLess.
have hSplit:I f-J f=(I f-I (test p))+(J (test p)-J f).
  by rewrite hAgreement; ring.
rewrite hSplit.
have hBound:=ler_normD (I f-I (test p)) (J (test p)-J f).
apply:le_lt_trans hBound _.
have hEtaHalf:eta<=epsilon/2 by rewrite /eta ge_min lexx.
lra.
Qed.
