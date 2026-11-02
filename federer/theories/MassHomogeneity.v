(** Federer (1969), 1.8.1, p. 38: supporting homogeneity of the mass norm.
    All arguments use the abstract dual laws. *)
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import InnerProductUP ExteriorGrading AlternatingCoordinates
  AlternatingPairing ComassUP MassUP MassBounds.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Section Homogeneity.
Variable R : rcfType.
Hypothesis h2 : (1+1 : R) != 0.
Variable V : lmodType R.
Variable B : V -> V -> R.
Hypothesis hB : is_inner_product B.
Variable m : nat.
Hypothesis hm : (0 < m)%N.
Variable kappa : A_m V R^o m -> R.
Hypothesis hk : forall phi, is_comass h2 hB phi (kappa phi).

(** Source for [mass_scale_upper]: Federer 1.8.1, p. 38,
    supporting one-sided homogeneity bound for the dual supremum. *)
Lemma mass_scale_upper (x : exterior_power V m) a d e :
  is_mass kappa x d -> is_mass kappa (a *: x) e -> e <= `|a| * d.
Proof.
move=> hd he; apply: (@mass_least_upper_bound R V m kappa (a *: x) e he (`|a| * d)) => phi hphi.
rewrite (bilZl (@pairing_bilinear R V R^o m)).
change (a * pairing x phi <= `|a| * d).
apply: (le_trans (ler_norm (a * pairing x phi))); rewrite normrM.
have hb := @mass_absolute_unit_bound R h2 V B hB m hm kappa hk x d hd phi hphi.
exact: (ler_wpM2l (normr_ge0 a) hb).
Qed.

(** Source for [mass_absolute_homogeneity]: Federer 1.8.1,
    p. 38, supporting norm law: mass(a*x)=|a| mass(x). *)
Theorem mass_absolute_homogeneity (x : exterior_power V m) a d e :
  is_mass kappa x d -> is_mass kappa (a *: x) e -> e = `|a| * d.
Proof.
move=> hd he; have [ha|ha] := eqVneq a 0.
- rewrite ha scale0r in he.
  have -> := mass_unique he (@mass_zero R h2 V B hB m hm kappa hk).
  by rewrite ha normr0 mul0r.
apply/eqP; rewrite eq_le; apply/andP; split; first exact: mass_scale_upper hd he.
have hax : a^-1 *: (a *: x) = x by rewrite scalerA mulVf // scale1r.
have hd' : is_mass kappa (a^-1 *: (a *: x)) d by rewrite hax.
have hh := mass_scale_upper he hd'.
have ht := ler_wpM2l (normr_ge0 a) hh.
rewrite normrV ?unitfE // in ht.
rewrite mulrA mulfV ?mul1r in ht; first exact ht.
by rewrite normr_eq0.
Qed.
End Homogeneity.
