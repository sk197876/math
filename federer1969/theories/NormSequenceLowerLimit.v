(** Federer (1969), 2.4.12, p. 87, lower-semicontinuity display: supporting
    scalar order and norm-continuity steps. Source context:
    MeasureEssentialNormUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric NormMetricContinuity ExtendedRealBoundsUP
  ExtendedRealOrderLimit ExtendedLowerLimitUP RealErrorOrderLimit.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [extended_lower_limit_pointwise_comparison]:
    supporting monotonicity of scalar lower limits used in
    Federer 2.4.12, p. 87. It follows directly
    from the eventual-bound supremum specification. *)
Lemma extended_lower_limit_pointwise_comparison (R : realType) (u v : nat -> \bar R) a b :
  is_extended_lower_limit u a -> is_extended_lower_limit v b ->
  (forall n, u n <= v n) -> a <= b.
Proof.
move=> ha hb huv; apply: (extended_real_supremum_least ha)=> c [N hN].
apply: (extended_lower_limit_eventual_bound hb); exists N=> n hn.
exact: le_trans (hN n hn) (huv n).
Qed.

(** Source for [norm_sequence_extended_order_limit]: supporting continuity
    of the norm in the lower-semicontinuity argument of Federer 2.4.12, p.
    87 No completeness is needed. *)
Lemma norm_sequence_extended_order_limit (R : realType) (V : lmodType R)
    (N : V -> R) (hN : is_real_norm N)
    (u : nat -> real_norm_metric_space hN) (z : real_norm_metric_space hN) :
  u @ \oo --> z -> extended_order_limit (fun n => (N (u n))%:E) (N z)%:E.
Proof.
move=> hl; apply: real_error_extended_order_limit=> e he.
have hn : nbhs z [set y | (mdist z y < e)%R].
  apply: (proj2 (metricType_numDomainType.nbhs_mdistP z _)); by exists e.
have [k _ hk] := hl _ hn; exists k=> n hkn.
have hdist := hk n hkn.
have hdist' : (N (z-u n)%R < e)%R := hdist.
rewrite distrC; exact: le_lt_trans (real_norm_change_bound hN z (u n)) hdist'.
Qed.
