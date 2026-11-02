(** Federer (1969), 2.4.14, p. 88: positive scaling of the normalised
    powered integrands. These supporting scalar laws use only the project's
    power definition and proved laws. *)
From mathcomp Require Import all_boot all_order all_algebra reals constructive_ereal.
From Federer Require Import RealPower ExtendedPositivePower.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope ereal_scope.

(** Source for [extended_positive_power_positive_scale]: scalar
    identity supporting normalisation in Federer 2.4.14,
    p. 88. The multiplying real scalar is positive;
    the nonnegative extended argument may be infinite. *)
Lemma extended_positive_power_positive_scale (R : realType) (c p : R) (x : \bar R) :
  (0 < c)%R -> (0 < p)%R -> 0 <= x ->
  extended_positive_power (c%:E*x) p =
    (real_power c p)%:E * extended_positive_power x p.
Proof.
move=> hc hp; case: x=> [x| |] hx.
- have hx0 : (0 <= x)%R := hx.
  by rewrite -EFinM /extended_positive_power /=
    (@real_power_product R c x p (ltW hc) hx0) EFinM.
- have hcE : (0 : \bar R) < c%:E by rewrite lte_fin.
  have hpowE : (0 : \bar R) < (real_power c p)%:E.
    rewrite lte_fin; exact: real_power_strictly_positive hc.
  by rewrite gt0_muley // /extended_positive_power gt0_muley.
- by move: hx.
Qed.
