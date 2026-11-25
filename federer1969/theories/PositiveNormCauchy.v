(** Federer (1969), 4.1.5, p. 349: the original
    convolution Cauchy estimate yields a finite positive-scale
    limit. This adapter uses the earlier complete norm-space
    Cauchy criterion rather than reconstructing completeness. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import RealNormUP NormMetric CompleteMetricUP NormedCurveDerivativeUP
  PuncturedNormCauchy PositiveNormLimitUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [positive_norm_cauchy]: the pairwise
    positive-scale estimate used to define T(w) in Federer
    4.1.5, p. 349. Values at nonpositive scales are irrelevant. *)
Definition positive_norm_cauchy (R:realType) (Y:lmodType R)
    (NY:Y->R) (u:R->Y):Prop:=
  forall eta:R,0<eta ->exists d:R,0<d /\ forall e f:R,
    0<e ->e<d ->0<f ->f<d ->NY (u e-u f)<eta.

(** Source for [positive_norm_cauchy_limit]: the actual finite
    limit of S(Phi_e*w) exists from the original pairwise
    estimate, Federer 4.1.5, p. 349. The general Banach
    target version follows from the earlier punctured criterion. *)
Theorem positive_norm_cauchy_limit (R:realType) (Y:lmodType R)
    (NY:Y->R) (hNY:is_real_norm NY)
    (hY:is_complete_metric_space (real_norm_metric_space hNY)) (u:R->Y):
  positive_norm_cauchy NY u ->exists v:Y,positive_norm_limit NY u v.
Proof.
move=>hC.
have hTwo:forall eta:R,0<eta ->exists d:R,0<d /\ forall e f:R,
    0<`|e|<d ->0<`|f|<d ->NY (u (`|e|)-u (`|f|))<eta.
  move=>eta hEta; have[d [hd hBound]]:=hC eta hEta.
  exists d; split=>// e f /andP [he hed] /andP [hf hfd].
  exact:(@hBound `|e| `|f| he hed hf hfd).
have[v hv]:=@punctured_norm_cauchy_limit R Y NY hNY hY (fun e=>u `|e|) hTwo.
exists v=>eta hEta.
have[d [hd hBound]]:=hv eta hEta.
exists d; split=>// e he hed.
have hAbs:0<`|e|<d by rewrite (ger0_norm (ltW he)); apply/andP; split.
have h:=hBound e hAbs.
by rewrite (ger0_norm (ltW he)) in h.
Qed.
