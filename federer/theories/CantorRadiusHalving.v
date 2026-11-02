(** Federer (1969), 2.10.29, p. 194: supporting geometric shrinkage of the
    two interval-length sequences, from the strict radius bound of
    2.10.28(4), p. 192. *)
From mathcomp Require Import all_boot all_order all_algebra reals lra.
From Federer Require Import CantorSplitRadiusUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [cantor_radius_halving_bound]: supporting
    s<=d/2 and s<d for each chosen child
    in the recursions of 2.10.29, p. 194.
    It holds for every specified split radius,
    without a power formula or implementation. *)
Lemma cantor_radius_halving_bound (R : realType) (h : R -> R) (d s : R) n :
  0<d -> (2<=n)%N -> is_cantor_split_radius h d n s -> s<=d/2 /\ s<d.
Proof.
move=> hd hn hs.
have hNR : (2<=n%:R :> R) by rewrite ler_nat.
have hN0 : (0<n%:R :> R) by lra.
have htwo : (0<2 :> R) by lra.
have hInv : (n%:R^-1<=2^-1 :> R) by rewrite (@lef_pV2 R n%:R 2 hN0 htwo).
have hdiv : d/n%:R<=d/2 := ler_wpM2l (ltW hd) hInv.
have hhalf := le_trans (ltW (cantor_split_radius_bounds hs).2) hdiv.
split=> //; have hlast : d/2<d by lra.
exact: le_lt_trans hhalf hlast.
Qed.
