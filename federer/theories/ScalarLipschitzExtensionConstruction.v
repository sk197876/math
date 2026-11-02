(** Supporting existence proof for the continuous extension in Federer
    (1969), 2.5.9, p. 100. We use the infimum of A(y)+d(x,y), with y in the
    original domain, to choose a scalar Lipschitz extension. This formula is
    an implementation choice for 2.5.9; Federer prints it later in 2.10.44,
    p. 202. Later arguments use only the sealed extension laws and density
    to obtain linearity. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal.
From Federer Require Import ScalarLipschitzExtensionUP ExtendedRealBoundsUP ExtendedRealBounds.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [scalar_lipschitz_extension_exists]: existence
    infrastructure for Federer 2.5.9, p. 100. Nonempty
    initial domain is required; pseudometric separation is not. *)
Theorem scalar_lipschitz_extension_exists (R : realType) (T : Type)
    (W D : set T) (d : T -> T -> R) (A : T -> R) :
  is_pseudometric_on_set W d -> (forall x, D x -> W x) -> (exists y, D y) ->
  is_scalar_lipschitz_on_set D d A ->
  exists B, is_scalar_lipschitz_extension W D d A B.
Proof.
move=> [hd0 [hdiag [hsym htri]]] hDW [a ha] hA.
pose S x := [set r : \bar R | exists y, D y /\ r=(A y+d x y)%R%:E].
pose F x := extended_real_inf (S x).
have hlo x : W x -> (A a-d x a)%R%:E <= F x.
  move=> hx; apply: extended_real_inf_greatest=> r [y [hy ->]].
  rewrite lee_fin lerBlDr.
  have hAy : (A a <= A y+d a y)%R.
    have hh := le_trans (ler_norm (A a-A y)) (hA a y ha hy).
    by move: hh; rewrite lerBlDr addrC.
  apply: le_trans hAy _; rewrite -addrA lerD2l.
  have ht := htri a x y (hDW a ha) hx (hDW y hy).
  by rewrite (hsym a x (hDW a ha) hx) addrC in ht.
have hup x y : D y -> F x <= (A y+d x y)%R%:E.
  move=> hy; apply: extended_real_inf_lower; by exists y.
have hfin x : W x -> F x \is a fin_num.
  move=> hx; rewrite fin_numElt; apply/andP; split.
  - exact: lt_le_trans (ltNyr _) (hlo x hx).
  - exact: le_lt_trans (hup x a ha) (ltry _).
pose B x := fine (F x).
have hBE x : W x -> (B x)%:E=F x by move=> hx; rewrite /B fineK //; exact: hfin.
have hupper x y : W x -> D y -> (B x <= A y+d x y)%R.
  move=> hx hy; have hh := hup x y hy; by rewrite -(hBE x hx) lee_fin in hh.
have hagree x : D x -> B x=A x.
  move=> hx; apply/eqP; rewrite eq_le; apply/andP; split.
  - have hh := hupper x x (hDW x hx) hx; by rewrite (hdiag x (hDW x hx)) addr0 in hh.
  - have hh : (A x)%:E <= F x.
      apply: extended_real_inf_greatest=> r [y [hy ->]]; rewrite lee_fin.
      have hh := le_trans (ler_norm (A x-A y)) (hA x y hx hy).
      by move: hh; rewrite lerBlDr addrC.
    by rewrite -(hBE x (hDW x hx)) lee_fin in hh.
have hdiff x z : W x -> W z -> (B x-B z <= d x z)%R.
  move=> hx hz.
  have hh : (B x-d x z)%R%:E <= F z.
    apply: extended_real_inf_greatest=> r [y [hy ->]]; rewrite lee_fin lerBlDr.
    apply: le_trans (hupper x y hx hy) _.
    have ht := htri x z y hx hz (hDW y hy).
    apply: le_trans (lerD (lexx (A y)) ht) _.
    by rewrite addrA addrAC.
  rewrite -(hBE z hz) lee_fin lerBlDr in hh.
  by move: hh; rewrite addrC -lerBlDr.
exists B; split=> // x z hx hz.
rewrite ler_norml; apply/andP; split.
- have hh := hdiff z x hz hx; rewrite (hsym z x hz hx) in hh.
  by rewrite -opprB lerN2.
- exact: hdiff x z hx hz.
Qed.
