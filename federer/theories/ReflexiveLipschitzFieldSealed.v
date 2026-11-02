(** Sealed bounded measurable weak derivative field for Federer (1969),
    2.9.22, p. 167. Source context and mathematical role:
    ReflexiveLipschitzFieldUP.v. The representative chosen off the common
    conull set and its existence construction are hidden; clients use only
    the bound, scalar derivative and measurability laws. This interface does
    not assert the subsequent norm differentiability theorem. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  cardinality reals constructive_ereal topology.
From Federer Require Import Hom RealNormUP NormMetric ContinuousDualUP ContinuousDualNorm
  ContinuousBidualUP LebesgueScalarMeasure ReflexiveLipschitzFieldUP
  ReflexiveLipschitzFieldConstruction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Module Type ReflexiveLipschitzFieldSignature.
(** Source for [value]: abstract measurable field v of
    Federer 2.9.22, p. 167, before the integral display. *)
Parameter value : forall (R : realType) (E D B : lmodType R)
    (N : E -> R) (hN : is_real_norm N)
    (ed : Hom D (Hom E R^o)) (DN : D -> R)
    (hD : is_continuous_dual hN ed DN)
    (eb : Hom B (Hom D R^o)) (BN : B -> R)
    (hB : is_continuous_dual (continuous_dual_norm_is_norm hD) eb BN)
    (tau : Hom E B) (g : R -> E) (L : R)
    (C : set (real_norm_metric_space hN))
    (ht : is_bidual_embedding ed eb tau) (hr : is_reflexive_embedding tau)
    (hCc : countable C) (hCd : dense C) (hL : 0<=L)
    (hg : forall t u, N (g t-g u)<=L * `|t-u|), R -> E.
(** Source for [laws]: boundedness, simultaneous scalar
    derivatives and measurability of v in Federer 2.9.22, p. 167. *)
Parameter laws : forall (R : realType) (E D B : lmodType R)
    (N : E -> R) (hN : is_real_norm N)
    (ed : Hom D (Hom E R^o)) (DN : D -> R)
    (hD : is_continuous_dual hN ed DN)
    (eb : Hom B (Hom D R^o)) (BN : B -> R)
    (hB : is_continuous_dual (continuous_dual_norm_is_norm hD) eb BN)
    (tau : Hom E B) (g : R -> E) (L : R)
    (C : set (real_norm_metric_space hN))
    (ht : is_bidual_embedding ed eb tau) (hr : is_reflexive_embedding tau)
    (hCc : countable C) (hCd : dense C) (hL : 0<=L)
    (hg : forall t u, N (g t-g u)<=L * `|t-u|),
  is_bounded_weak_derivative_field hN ed (@lebesgue_scalar_measure R) g
    (@value R E D B N hN ed DN hD eb BN hB tau g L C ht hr hCc hCd hL hg) L.
End ReflexiveLipschitzFieldSignature.

Module ReflexiveLipschitzField : ReflexiveLipschitzFieldSignature.
(** Source for [value]: private selection of the proved
    measurable-field witness for Federer 2.9.22, p. 167. *)
Definition value (R : realType) (E D B : lmodType R)
    (N : E -> R) (hN : is_real_norm N)
    (ed : Hom D (Hom E R^o)) (DN : D -> R)
    (hD : is_continuous_dual hN ed DN)
    (eb : Hom B (Hom D R^o)) (BN : B -> R)
    (hB : is_continuous_dual (continuous_dual_norm_is_norm hD) eb BN)
    (tau : Hom E B) (g : R -> E) (L : R)
    (C : set (real_norm_metric_space hN))
    (ht : is_bidual_embedding ed eb tau) (hr : is_reflexive_embedding tau)
    (hCc : countable C) (hCd : dense C) (hL : 0<=L)
    (hg : forall t u, N (g t-g u)<=L * `|t-u|) :=
  projT1 (cid (@reflexive_lipschitz_field_exists R E D B N hN ed DN hD eb BN hB tau g L C ht hr hCc hCd hL hg)).
(** Source for [laws]: the selected witness satisfies the
    abstract field laws for Federer 2.9.22, p. 167. *)
Lemma laws (R : realType) (E D B : lmodType R)
    (N : E -> R) (hN : is_real_norm N)
    (ed : Hom D (Hom E R^o)) (DN : D -> R)
    (hD : is_continuous_dual hN ed DN)
    (eb : Hom B (Hom D R^o)) (BN : B -> R)
    (hB : is_continuous_dual (continuous_dual_norm_is_norm hD) eb BN)
    (tau : Hom E B) (g : R -> E) (L : R)
    (C : set (real_norm_metric_space hN))
    (ht : is_bidual_embedding ed eb tau) (hr : is_reflexive_embedding tau)
    (hCc : countable C) (hCd : dense C) (hL : 0<=L)
    (hg : forall t u, N (g t-g u)<=L * `|t-u|) :
  is_bounded_weak_derivative_field hN ed (@lebesgue_scalar_measure R) g
    (@value R E D B N hN ed DN hD eb BN hB tau g L C ht hr hCc hCd hL hg) L.
Proof.
exact: projT2 (cid (@reflexive_lipschitz_field_exists R E D B N hN ed DN hD eb BN hB tau g L C ht hr hCc hCd hL hg)).
Qed.
End ReflexiveLipschitzField.
