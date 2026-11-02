(** Federer (1969), 1.8.1, p. 38: supporting absolute homogeneity of the
    comass norm. The proof uses only supremum laws and symmetry of S. *)
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import InnerProductUP AlternatingCoordinates AlternatingPairing
  SimpleUnitBall ComassUP ComassBounds.
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

(** Source for [comass_scale_upper]: Federer 1.8.1, p. 38,
    supporting one-sided scalar bound for the norm specified as a supremum. *)
Lemma comass_scale_upper (phi : A_m V R^o m) a c d :
  is_comass h2 hB phi c -> is_comass h2 hB (a *: phi) d -> d <= `|a| * c.
Proof.
move=> hc hd; apply: (@comass_least_upper_bound R h2 V B hB m (a *: phi) d hd (`|a| * c)) => x hx.
rewrite (bilZr (@pairing_bilinear R V R^o m)).
change (a * pairing x phi <= `|a| * c).
apply: (le_trans (ler_norm (a * pairing x phi))).
rewrite normrM.
have hb := @comass_absolute_unit_bound R h2 V B hB m hm phi c hc x hx.
exact: (ler_wpM2l (normr_ge0 a) hb).
Qed.

(** Source for [comass_absolute_homogeneity]: Federer 1.8.1,
    p. 38, supporting norm law: scalar multiplication scales the
    comass by the absolute value of the scalar. *)
Theorem comass_absolute_homogeneity (phi : A_m V R^o m) a c d :
  is_comass h2 hB phi c -> is_comass h2 hB (a *: phi) d -> d = `|a| * c.
Proof.
move=> hc hd; have [ha|ha] := eqVneq a 0.
- rewrite ha scale0r in hd.
  have -> := comass_unique hd (comass_zero h2 hB hm).
  by rewrite ha normr0 mul0r.
apply/eqP; rewrite eq_le; apply/andP; split; first exact: comass_scale_upper hc hd.
have hk : a^-1 *: (a *: phi) = phi by rewrite scalerA mulVf // scale1r.
have hc' : is_comass h2 hB (a^-1 *: (a *: phi)) c by rewrite hk.
have hh := comass_scale_upper hd hc'.
have ht := ler_wpM2l (normr_ge0 a) hh.
rewrite normrV ?unitfE // in ht.
rewrite mulrA mulfV ?mul1r in ht; first exact ht.
by rewrite normr_eq0.
Qed.
End Homogeneity.
