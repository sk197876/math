(** Federer (1969), 1.8.1, p. 38: mass is supplied by its supremum laws,
    with its existence witness hidden by opaque module ascription. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp.
From Federer Require Import InnerProductUP ExteriorGrading AlternatingCoordinates
  LinearBasis ComassUP MassUP MassConstruction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Module Type MassSig.
(** Source for [norm]: Federer 1.8.1, p. 38, the mass
    of a positive-degree multivector, dual to a specified comass function. *)
Parameter norm : forall (R : realType) (h2 : (1+1 : R) != 0)
    (V : lmodType R) (B : V -> V -> R) (hB : is_inner_product B)
    n (e : 'I_n -> V), is_basis e -> forall m, (0 < m)%N ->
    forall kappa : A_m V R^o m -> R,
    (forall phi, is_comass h2 hB phi (kappa phi)) -> exterior_power V m -> R.
(** Source for [laws]: Federer 1.8.1, p. 38,
    the exported mass satisfies its dual supremum specification. *)
Parameter laws : forall (R : realType) (h2 : (1+1 : R) != 0)
    (V : lmodType R) (B : V -> V -> R) (hB : is_inner_product B)
    n (e : 'I_n -> V) (he : is_basis e) m (hm : (0 < m)%N)
    (kappa : A_m V R^o m -> R) (hk : forall phi, is_comass h2 hB phi (kappa phi))
    (x : exterior_power V m),
    is_mass kappa x (@norm R h2 V B hB n e he m hm kappa hk x).
End MassSig.
Module Mass : MassSig.
(** Source for [norm]: Federer 1.8.1, p. 38,
    select the proved mass witness inside the sealed module. *)
Definition norm (R : realType) (h2 : (1+1 : R) != 0)
    (V : lmodType R) (B : V -> V -> R) (hB : is_inner_product B)
    n (e : 'I_n -> V) (he : is_basis e) m (hm : (0 < m)%N)
    (kappa : A_m V R^o m -> R) (hk : forall phi, is_comass h2 hB phi (kappa phi))
    (x : exterior_power V m) : R :=
  sval (constructive_indefinite_description (@mass_exists R h2 V B hB n e he m hm kappa hk x)).
(** Source for [laws]: Federer 1.8.1, p. 38,
    the selected witness obeys the public mass specification. *)
Lemma laws (R : realType) (h2 : (1+1 : R) != 0)
    (V : lmodType R) (B : V -> V -> R) (hB : is_inner_product B)
    n (e : 'I_n -> V) (he : is_basis e) m (hm : (0 < m)%N)
    (kappa : A_m V R^o m -> R) (hk : forall phi, is_comass h2 hB phi (kappa phi))
    (x : exterior_power V m) :
    is_mass kappa x (@norm R h2 V B hB n e he m hm kappa hk x).
Proof. exact: (svalP (constructive_indefinite_description (@mass_exists R h2 V B hB n e he m hm kappa hk x))). Qed.
End Mass.
