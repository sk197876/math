(** Federer (1969), 2.4.12, p. 87: norms raised to a positive power converge
    pointwise when the original vectors converge. Supporting continuity uses
    only the norm laws and the proved scalar order-limit laws. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric PartialFunctionUP PartialFunctionLimitUP
  PartialDominatedConvergence PartialNormPower NormSequenceLowerLimit
  ExtendedPositivePower ExtendedPositivePowerLimit.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [partial_norm_power_convergence_locus]: supporting
    passage from vector convergence to powered norms in Federer
    2.4.12, p. 87. This pointwise statement retains
    all graph values and requires no measure or completeness. *)
Lemma partial_norm_power_convergence_locus (R : realType) (X : Type)
    (V : lmodType R) (N : V -> R) (hN : is_real_norm N) (p : R)
    (f : nat -> partial_function X (real_norm_metric_space hN))
    (g : partial_function X (real_norm_metric_space hN)) :
  (0 < p)%R -> partial_function_limit_locus f g `<=`
    partial_extended_convergence_locus (fun n => partial_norm_power N p (f n))
      (partial_norm_power N p g).
Proof.
move=> hp x [u [z [hu [hz hl]]]].
exists (fun n => extended_positive_power (N (u n))%:E p),
  (extended_positive_power (N z)%:E p); split.
- move=> n; exists (u n); by split.
- split; first by exists z; split.
  apply: (@extended_positive_power_order_limit R (fun n => (N (u n))%:E) (N z)%:E p).
  + move=> n; rewrite lee_fin; exact (real_seminorm_nonnegative hN.1 (u n)).
  + rewrite lee_fin; exact (real_seminorm_nonnegative hN.1 z).
  + exact hp.
  + exact (@norm_sequence_extended_order_limit R V N hN u z hl).
Qed.
