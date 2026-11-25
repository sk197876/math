(** Federer (1969), 1.8.1, p. 38: the duality of mass and comass gives the
    homogeneous evaluation bound. This supporting result is derived from the
    two supremum specifications. *)
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import InnerProductUP ExteriorGrading AlternatingCoordinates
  AlternatingPairing ComassUP ComassBounds ComassHomogeneity MassUP MassBounds.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Section Pairing.
Variable R : rcfType.
Hypothesis h2 : (1+1 : R) != 0.
Variable V : lmodType R.
Variable B : V -> V -> R.
Hypothesis hB : is_inner_product B.
Variable m : nat.
Hypothesis hm : (0 < m)%N.
Variable kappa : A_m V R^o m -> R.
Hypothesis hk : forall phi, is_comass h2 hB phi (kappa phi).

(** Source for [mass_comass_pairing_bound]: Federer 1.8.1,
    p. 38, supporting dual norm inequality: absolute evaluation is
    bounded by mass times comass. No finite-dimensional hypothesis
    is needed when the two specified norms exist. *)
Theorem mass_comass_pairing_bound x d (hd : is_mass kappa x d) (phi : A_m V R^o m) :
  `|pairing x phi| <= d * kappa phi.
Proof.
have [->|hphi] := eqVneq phi 0.
- by rewrite (bil0r (@pairing_bilinear R V R^o m)) normr0
    (@comass_function_zero R h2 V B hB m hm kappa hk) mulr0.
have hc0 : 0 <= kappa phi := comass_nonnegative hm (hk phi).
have hc : kappa phi != 0.
  apply/eqP=> hz; apply: (elimT negP hphi); apply/eqP.
  apply: (@comass_definite R h2 V B hB m hm phi).
  by rewrite -hz.
pose psi := (kappa phi)^-1 *: phi.
have hpsi : kappa psi = 1.
  have hh := @comass_absolute_homogeneity R h2 V B hB m hm phi
    (kappa phi)^-1 (kappa phi) (kappa psi) (hk phi) (hk psi).
  have hi : 0 <= (kappa phi)^-1 by rewrite invr_ge0.
  by rewrite (ger0_norm hi) mulVf // in hh.
have hp1 : kappa psi <= 1 by rewrite hpsi.
have hb := @mass_absolute_unit_bound R h2 V B hB m hm kappa hk x d hd psi hp1.
have ht := ler_wpM2l hc0 hb.
rewrite -(ger0_norm hc0) -normrM in ht.
have hp : kappa phi * pairing x psi = pairing x phi.
  change ((kappa phi *: pairing x psi : R^o) = pairing x phi).
  by rewrite -(bilZr (@pairing_bilinear R V R^o m)) /psi scalerA mulfV // scale1r.
by rewrite hp (ger0_norm hc0) mulrC in ht.
Qed.
End Pairing.
