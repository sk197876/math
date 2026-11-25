(** Supporting Federer (1969), 3.4.12, p. 339, extending 3.4.8(5), p. 328:
    continuous families retain the original holomorphic
    germ-ring arithmetic. The operation continuity was
    proved for the metric in 3.4.5, p. 319. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import ScalarRestriction ComplexScalarSealed RealNormUP HolomorphicGermRing HolomorphicGermMetric
  HolomorphicGermAddContinuity HolomorphicGermNegateContinuity HolomorphicGermMultiplyContinuity
  ContinuousCommonPair.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section Families.
Variable R:realType.
Variable X:lmodType (ComplexScalars.C R).
Variable NX:X->R.
Variable hNX:@is_real_norm R (restricted_space (ComplexScalars.embed R) X) NX.
Variable a:X.
Variable T:topologicalType.
Local Notation M:=(@holomorphic_germ_metric R X NX hNX a).
Local Notation G:=[the comNzRingType of (@holomorphic_germ_ring R X NX hNX a)].
Variables f g:T->M.

(** Source for [holomorphic_germ_parameter_add_continuous]:
    continuous families may be added in the original
    germ metric, supporting 3.4.8(5), p. 328,
    from 3.4.5, p. 319. *)
Lemma holomorphic_germ_parameter_add_continuous:
  continuous f ->continuous g ->continuous (fun t:T=>((f t:G)+(g t:G):M)).
Proof.
move=>hf hg.
have hPair:=@continuous_common_domain_pair T M M f g hf hg.
move=>t;exact:(continuous_comp (hPair t)
  (@holomorphic_germ_add_continuous R X NX hNX a (f t,g t))).
Qed.

(** Source for [holomorphic_germ_parameter_negate_continuous]:
    continuous germ families retain continuity under
    negation, supporting the same original assertions. *)
Lemma holomorphic_germ_parameter_negate_continuous:
  continuous f ->continuous (fun t:T=>(-(f t:G):M)).
Proof.
move=>hf t;exact:(continuous_comp (hf t)
  (@holomorphic_germ_negate_continuous R X NX hNX a (f t))).
Qed.

(** Source for [holomorphic_germ_parameter_subtract_continuous]:
    continuous germ families may be subtracted,
    supporting the same original assertions. *)
Lemma holomorphic_germ_parameter_subtract_continuous:
  continuous f ->continuous g ->continuous (fun t:T=>((f t:G)-(g t:G):M)).
Proof.
move=>hf hg.
have hNeg:continuous (fun t:T=>(-(g t:G):M)).
  move=>t;exact:(continuous_comp (hg t)
    (@holomorphic_germ_negate_continuous R X NX hNX a (g t))).
have hPair:=@continuous_common_domain_pair T M M f (fun t:T=>(-(g t:G):M)) hf hNeg.
move=>t;exact:(continuous_comp (hPair t)
  (@holomorphic_germ_add_continuous R X NX hNX a (f t,-(g t:G)))).
Qed.

(** Source for [holomorphic_germ_parameter_multiply_continuous]:
    continuous germ families retain the actual product,
    supporting 3.4.8(5), p. 328, from the
    ring topology of 3.4.5, p. 319. *)
Lemma holomorphic_germ_parameter_multiply_continuous:
  continuous f ->continuous g ->continuous (fun t:T=>((f t:G)*(g t:G):M)).
Proof.
move=>hf hg.
have hPair:=@continuous_common_domain_pair T M M f g hf hg.
move=>t;exact:(continuous_comp (hPair t)
  (@holomorphic_germ_multiply_continuous R X NX hNX a (f t,g t))).
Qed.
End Families.
