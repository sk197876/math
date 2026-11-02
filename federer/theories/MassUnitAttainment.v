(** Federer (1969), 1.8.4, p. 41: the mass-attaining covector may be chosen
    with comass exactly one when the mass is positive. The closed-ball
    version remains valid without this hypothesis; in zero exterior
    dimension no unit covector exists. Source context and supporting
    duality: MassAttainment.v. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import InnerProductUP ExteriorGrading AlternatingCoordinates
  AlternatingPairing LinearBasis ComassUP MassUP MassPairingBound MassAttainment.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [positive_mass_attained_on_comass_sphere]: Federer
    1.8.4, p. 41, the choice of a covector of unit comass
    pairing to the mass. Positivity of the mass rules out the
    degenerate exterior space and forces every maximizer onto the sphere. *)
Theorem positive_mass_attained_on_comass_sphere (R : realType)
    (h2 : (1+1 : R) != 0) (V : lmodType R) (B : V -> V -> R)
    (hB : is_inner_product B) n (e : 'I_n -> V) (he : is_basis e)
    m (hm : (0 < m)%N) (kappa : A_m V R^o m -> R)
    (hk : forall phi, is_comass h2 hB phi (kappa phi))
    (x : exterior_power V m) d (hd : is_mass kappa x d) (hd0 : 0 < d) :
  exists phi, kappa phi = 1 /\ pairing x phi = d.
Proof.
have [phi [hp hxp]] := @mass_attained R h2 V B hB n e he m hm kappa hk x d hd.
exists phi; split=> //; apply/eqP; rewrite eq_le; apply/andP; split=> //.
have hh := @mass_comass_pairing_bound R h2 V B hB m hm kappa hk x d hd phi.
rewrite hxp ger0_norm ?(ltW hd0) // in hh.
by rewrite -(ler_pM2l hd0) mulr1.
Qed.
