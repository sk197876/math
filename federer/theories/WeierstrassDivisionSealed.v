(** Federer (1969), 3.4.6(1), p. 322: opaque
    analytic division, exposed through the original germ
    equation, neighbourhood derivative condition and uniqueness. *)
From mathcomp Require Import all_boot all_order all_algebra boolp reals topology.
From Federer Require Import RealNormUP NormMetric CompleteMetricUP AnalyticGermUP AnalyticGermRing
  WeierstrassRegularUP WeierstrassDivisionUP WeierstrassDivision.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Module Type WeierstrassDivisionSignature.
(** Source for [quotient]: the original quotient germ,
    3.4.6(1), p. 322. *)
Parameter quotient:forall (R:realType) (X:lmodType R) (NX:X->R) (hNX:is_real_norm NX)
  (hComplete:is_complete_metric_space [the metricType R of real_norm_metric_space hNX])
  k (v:X) (Phi Psi:@analytic_germ_ring R X NX hNX 0)
  (hRegular:is_weierstrass_regular_germ Phi k v),
  @analytic_germ_ring R X NX hNX 0.
(** Source for [remainder]: the original remainder germ,
    3.4.6(1), p. 322. *)
Parameter remainder:forall (R:realType) (X:lmodType R) (NX:X->R) (hNX:is_real_norm NX)
  (hComplete:is_complete_metric_space [the metricType R of real_norm_metric_space hNX])
  k (v:X) (Phi Psi:@analytic_germ_ring R X NX hNX 0)
  (hRegular:is_weierstrass_regular_germ Phi k v),
  @analytic_germ_ring R X NX hNX 0.
(** Source for [laws]: the original division identity
    and actual polynomial remainder, 3.4.6(1), p. 322. *)
Parameter laws:forall (R:realType) (X:lmodType R) (NX:X->R) (hNX:is_real_norm NX)
  (hComplete:is_complete_metric_space [the metricType R of real_norm_metric_space hNX])
  k (v:X) (Phi Psi:@analytic_germ_ring R X NX hNX 0)
  (hRegular:is_weierstrass_regular_germ Phi k v),
  @is_weierstrass_division R X NX hNX k v Phi Psi
    (@quotient R X NX hNX hComplete k v Phi Psi hRegular) (@remainder R X NX hNX hComplete k v Phi Psi hRegular).
(** Source for [unique]: both original division germs
    are uniquely determined, 3.4.6(1), p. 322. *)
Parameter unique:forall (R:realType) (X:lmodType R) (NX:X->R) (hNX:is_real_norm NX)
  (hComplete:is_complete_metric_space [the metricType R of real_norm_metric_space hNX])
  k (v:X) (Phi Psi:@analytic_germ_ring R X NX hNX 0)
  (hRegular:is_weierstrass_regular_germ Phi k v),
  forall Q T,@is_weierstrass_division R X NX hNX k v Phi Psi Q T ->
    Q=@quotient R X NX hNX hComplete k v Phi Psi hRegular /\T=@remainder R X NX hNX hComplete k v Phi Psi hRegular.
End WeierstrassDivisionSignature.
Module WeierstrassDivision:WeierstrassDivisionSignature.
Section Parameters.
Variable R:realType.
Variable X:lmodType R.
Variable NX:X->R.
Variable hNX:is_real_norm NX.
Variable hComplete:is_complete_metric_space [the metricType R of real_norm_metric_space hNX].
Variable k:nat.
Variable v:X.
Variables Phi Psi:@analytic_germ_ring R X NX hNX 0.
Variable hRegular:is_weierstrass_regular_germ Phi k v.
Let witness:=cid (@weierstrass_division R X NX hNX hComplete k v Phi Psi hRegular).
(** Source for [quotient]: a private witness of proved
    analytic division, 3.4.6(1), p. 322. *)
Definition quotient:@analytic_germ_ring R X NX hNX 0:=projT1 witness.
Let remainder_witness:=cid (projT2 witness).
(** Source for [remainder]: a private witness of proved
    analytic division, 3.4.6(1), p. 322. *)
Definition remainder:@analytic_germ_ring R X NX hNX 0:=projT1 remainder_witness.
(** Source for [laws]: the witnesses satisfy the original
    independent division laws, 3.4.6(1), p. 322. *)
Lemma laws:@is_weierstrass_division R X NX hNX k v Phi Psi quotient remainder.
Proof. exact:(projT2 remainder_witness).1. Qed.
(** Source for [unique]: every original division candidate
    agrees with the opaque witnesses, 3.4.6(1), p. 322. *)
Lemma unique Q T:@is_weierstrass_division R X NX hNX k v Phi Psi Q T ->
    Q=quotient /\T=remainder.
Proof. exact:(projT2 remainder_witness).2 Q T. Qed.
End Parameters.
End WeierstrassDivision.
