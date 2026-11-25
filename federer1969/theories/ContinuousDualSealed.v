(** Opaque continuous-dual interface for Federer (1969), 2.4.12,
    p. 87. The carrier and supremum implementations are hidden;
    downstream proofs use only ContinuousDualUP.v and its proved laws. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import Hom RealNormUP ContinuousDualUP ContinuousDualConstruction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module Type ContinuousDualSignature.
(** Source for [space]: Y* in Federer 2.4.12, p. 87. *)
Parameter space : forall (R : realType) (V : lmodType R)
  (N : V -> R), is_real_norm N -> lmodType R.
(** Source for [evaluation]: the pairing of Y* with Y,
    Federer 2.4.12, p. 87. *)
Parameter evaluation : forall (R : realType) (V : lmodType R)
  (N : V -> R) (hN : is_real_norm N), Hom (@space R V N hN) (Hom V R^o).
(** Source for [norm]: the dual norm, Federer 2.4.12, p. 87. *)
Parameter norm : forall (R : realType) (V : lmodType R)
  (N : V -> R) (hN : is_real_norm N), @space R V N hN -> R.
(** Source for [laws]: the dual specification, Federer 2.4.12, p. 87. *)
Parameter laws : forall (R : realType) (V : lmodType R)
  (N : V -> R) (hN : is_real_norm N),
  is_continuous_dual hN (@evaluation R V N hN) (@norm R V N hN).
End ContinuousDualSignature.

Module ContinuousDual : ContinuousDualSignature.
(** Source for [space]: sealed carrier witness for Y*,
    Federer 2.4.12, p. 87. *)
Definition space (R : realType) (V : lmodType R)
  (N : V -> R) (hN : is_real_norm N) := continuous_dual_carrier hN.
(** Source for [evaluation]: sealed evaluation witness,
    Federer 2.4.12, p. 87. *)
Definition evaluation (R : realType) (V : lmodType R)
  (N : V -> R) (hN : is_real_norm N) := continuous_dual_evaluation hN.
(** Source for [norm]: sealed dual norm witness,
    Federer 2.4.12, p. 87. *)
Definition norm (R : realType) (V : lmodType R)
  (N : V -> R) (hN : is_real_norm N) := continuous_dual_carrier_norm (hN:=hN).
(** Source for [laws]: verified dual laws,
    Federer 2.4.12, p. 87. *)
Lemma laws (R : realType) (V : lmodType R)
  (N : V -> R) (hN : is_real_norm N) :
  is_continuous_dual hN (evaluation hN) (norm (hN:=hN)).
Proof. exact: continuous_dual_carrier_laws. Qed.
End ContinuousDual.
