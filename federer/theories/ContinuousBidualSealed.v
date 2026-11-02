(** Sealed canonical bidual map for Federer (1969), 2.4.12, p. 87. Source
    context: ContinuousBidualUP.v. Only the defining evaluation identity is
    exposed; isometry and reflexivity are derived from it without inspecting
    the chosen representative. *)
From mathcomp Require Import all_boot all_order all_algebra boolp reals.
From Federer Require Import Hom RealNormUP ContinuousDualUP ContinuousDualNorm
  ContinuousBidualUP ContinuousBidualConstruction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module Type ContinuousBidualSignature.
(** Source for [value]: the canonical map tau, Federer 2.4.12, p. 87. *)
Parameter value : forall (R : realType) (V D B : lmodType R)
    (N : V -> R) (hN : is_real_norm N)
    (ed : Hom D (Hom V R^o)) (DN : D -> R)
    (hD : is_continuous_dual hN ed DN)
    (eb : Hom B (Hom D R^o)) (BN : B -> R)
    (hB : is_continuous_dual (continuous_dual_norm_is_norm hD) eb BN), Hom V B.
(** Source for [laws]: the defining evaluation identity,
    Federer 2.4.12, p. 87. *)
Parameter laws : forall (R : realType) (V D B : lmodType R)
    (N : V -> R) (hN : is_real_norm N)
    (ed : Hom D (Hom V R^o)) (DN : D -> R)
    (hD : is_continuous_dual hN ed DN)
    (eb : Hom B (Hom D R^o)) (BN : B -> R)
    (hB : is_continuous_dual (continuous_dual_norm_is_norm hD) eb BN),
  is_bidual_embedding ed eb (@value R V D B N hN ed DN hD eb BN hB).
End ContinuousBidualSignature.

Module ContinuousBidual : ContinuousBidualSignature.
(** Source for [value]: chosen witness of the proved bidual-map
    existence, Federer 2.4.12, p. 87. *)
Definition value (R : realType) (V D B : lmodType R)
    (N : V -> R) (hN : is_real_norm N)
    (ed : Hom D (Hom V R^o)) (DN : D -> R)
    (hD : is_continuous_dual hN ed DN)
    (eb : Hom B (Hom D R^o)) (BN : B -> R)
    (hB : is_continuous_dual (continuous_dual_norm_is_norm hD) eb BN) :=
  projT1 (cid (continuous_bidual_embedding_exists hB)).
(** Source for [laws]: verified identity of the chosen map,
    Federer 2.4.12, p. 87. *)
Lemma laws (R : realType) (V D B : lmodType R)
    (N : V -> R) (hN : is_real_norm N)
    (ed : Hom D (Hom V R^o)) (DN : D -> R)
    (hD : is_continuous_dual hN ed DN)
    (eb : Hom B (Hom D R^o)) (BN : B -> R)
    (hB : is_continuous_dual (continuous_dual_norm_is_norm hD) eb BN) :
  is_bidual_embedding ed eb (value hB).
Proof. exact: projT2 (cid (continuous_bidual_embedding_exists hB)). Qed.
End ContinuousBidual.
