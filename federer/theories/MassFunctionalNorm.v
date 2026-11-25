(** Federer (1969), 4.1.7, p. 357: the
    mass is exactly the functional norm dual to
    comass. This is the 1.8.1 supremum rewritten
    in the independent norm specification of 2.4.12. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import InnerProductUP ExteriorGrading AlternatingForms
  AlternatingPairing PairingLinear ComassUP MassUP MassBounds MassPairingBound
  RealFunctionalNormUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [mass_is_pairing_functional_norm]: the
    original mass/comass duality used in Federer
    4.1.7, p. 357, from 1.8.1, p. 38. *)
Theorem mass_is_pairing_functional_norm (R:realType) (h2:(1+1:R)!=0)
    (V:lmodType R) (B:V->V->R) (hB:is_inner_product B) m (hm:(0<m)%N)
    (kappa:A_m V R^o m->R) (hk:forall phi,is_comass h2 hB phi (kappa phi))
    (xi:exterior_power V m) d:
  is_mass kappa xi d ->is_real_functional_norm kappa (pairing_right xi) d.
Proof.
move=>hd; constructor.
- exact:(@mass_nonnegative R h2 V B hB m hm kappa hk xi d hd).
- move=>phi; exact:(@mass_comass_pairing_bound R h2 V B hB m hm kappa hk xi d hd phi).
- move=>C hC hb.
  apply:(@mass_least_upper_bound R V m kappa xi d hd C)=>phi hphi.
  have h:=le_trans (ler_norm (pairing xi phi)) (hb phi).
  apply:(le_trans h).
  have hh:=ler_wpM2l hC hphi.
  by rewrite mulr1 in hh.
Qed.
