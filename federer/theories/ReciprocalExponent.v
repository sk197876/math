(** Federer (1969), 2.4.17, p. 90: reciprocal exponent coordinates, with
    1/0=infinity. These supporting order laws keep zero separate from
    ordinary field inversion, whose value at zero is not infinity. *)
From mathcomp Require Import all_boot all_order all_algebra reals constructive_ereal.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope ereal_scope.

(** Source for [reciprocal_lebesgue_exponent]: the explicit
    convention 1/0=infinity in Federer 2.4.17, p. 90. *)
Definition reciprocal_lebesgue_exponent (R : realType) (u : R) : \bar R :=
  if u == 0%R then +oo else (u^-1)%:E.

(** Source for [reciprocal_lebesgue_exponent_domain]: [0,1]
    corresponds to the allowed norm exponents [1,infinity], supporting
    the sets P and U in Federer 2.4.17, p. 90. *)
Lemma reciprocal_lebesgue_exponent_domain (R : realType) (u : R) :
  (0 <= u)%R -> (u <= 1)%R -> 1 <= reciprocal_lebesgue_exponent u.
Proof.
move=> hu hu1; rewrite /reciprocal_lebesgue_exponent; case: ifP=> hz; first exact: leey.
have hup : (0 < u)%R by rewrite lt_neqAle eq_sym hz hu.
by rewrite lee_fin invf_ge1.
Qed.

(** Source for [reciprocal_lebesgue_exponent_antitone]: order
    reversal for the reciprocal coordinate in Federer 2.4.17,
    p. 90, including the infinity endpoint. *)
Lemma reciprocal_lebesgue_exponent_antitone (R : realType) (u v : R) :
  (0 <= u)%R -> (u <= v)%R -> reciprocal_lebesgue_exponent v <= reciprocal_lebesgue_exponent u.
Proof.
move=> hu huv; rewrite /reciprocal_lebesgue_exponent.
have [huz|hun] := eqVneq u 0%R; first exact: leey.
have hup : (0 < u)%R by rewrite lt_neqAle eq_sym hun hu.
have hvp : (0 < v)%R := lt_le_trans hup huv.
by rewrite (gt_eqF hvp) lee_fin lef_pV2 ?inE.
Qed.
