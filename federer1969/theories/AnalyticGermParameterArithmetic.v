(** Supporting Federer (1969), 3.4.8(5), p. 328:
    continuous families retain the original analytic
    germ-ring arithmetic. The operation continuity was
    proved for the metric in 3.4.5, p. 319. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import RealNormUP AnalyticGermRing AnalyticGermMetric
  AnalyticGermAddContinuity AnalyticGermNegateContinuity AnalyticGermMultiplyContinuity
  ContinuousCommonPair.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section Families.
Variable R:realType.
Variable X:lmodType R.
Variable NX:X->R.
Variable hNX:is_real_norm NX.
Variable a:X.
Variable T:topologicalType.
Local Notation M:=(@analytic_germ_metric R X NX hNX a).
Local Notation G:=[the comNzRingType of (@analytic_germ_ring R X NX hNX a)].
Variables f g:T->M.

(** Source for [analytic_germ_parameter_add_continuous]:
    continuous families may be added in the original
    germ metric, supporting 3.4.8(5), p. 328,
    from 3.4.5, p. 319. *)
Lemma analytic_germ_parameter_add_continuous:
  continuous f ->continuous g ->continuous (fun t:T=>((f t:G)+(g t:G):M)).
Proof.
move=>hf hg.
have hPair:=@continuous_common_domain_pair T M M f g hf hg.
move=>t;exact:(continuous_comp (hPair t)
  (@analytic_germ_add_continuous R X NX hNX a (f t,g t))).
Qed.

(** Source for [analytic_germ_parameter_negate_continuous]:
    continuous germ families retain continuity under
    negation, supporting the same original assertions. *)
Lemma analytic_germ_parameter_negate_continuous:
  continuous f ->continuous (fun t:T=>(-(f t:G):M)).
Proof.
move=>hf t;exact:(continuous_comp (hf t)
  (@analytic_germ_negate_continuous R X NX hNX a (f t))).
Qed.

(** Source for [analytic_germ_parameter_subtract_continuous]:
    continuous germ families may be subtracted,
    supporting the same original assertions. *)
Lemma analytic_germ_parameter_subtract_continuous:
  continuous f ->continuous g ->continuous (fun t:T=>((f t:G)-(g t:G):M)).
Proof.
move=>hf hg.
have hNeg:continuous (fun t:T=>(-(g t:G):M)).
  move=>t;exact:(continuous_comp (hg t)
    (@analytic_germ_negate_continuous R X NX hNX a (g t))).
have hPair:=@continuous_common_domain_pair T M M f (fun t:T=>(-(g t:G):M)) hf hNeg.
move=>t;exact:(continuous_comp (hPair t)
  (@analytic_germ_add_continuous R X NX hNX a (f t,-(g t:G)))).
Qed.

(** Source for [analytic_germ_parameter_multiply_continuous]:
    continuous germ families retain the actual product,
    supporting 3.4.8(5), p. 328, from the
    ring topology of 3.4.5, p. 319. *)
Lemma analytic_germ_parameter_multiply_continuous:
  continuous f ->continuous g ->continuous (fun t:T=>((f t:G)*(g t:G):M)).
Proof.
move=>hf hg.
have hPair:=@continuous_common_domain_pair T M M f g hf hg.
move=>t;exact:(continuous_comp (hPair t)
  (@analytic_germ_multiply_continuous R X NX hNX a (f t,g t))).
Qed.
End Families.
