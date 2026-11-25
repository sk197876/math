(** Federer (1969), 3.2.22, p. 260:
    multiply the Hausdorff fibre comparisons by the
    target-chart area factor, including infinite masses. *)
From mathcomp Require Import all_boot all_order all_algebra reals constructive_ereal.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope ereal_scope.

(** Source for [extended_fibre_product_bounds]: supporting
    the second local comparison in Federer 3.2.22,
    p. 260. Two fibre masses comparable by p
    remain comparable after multiplying the first by
    a target density between 1/t and t, at
    the factor p times t. Zero and infinite
    masses retain the distinguished zero-product convention. *)
Lemma extended_fibre_product_bounds (R:realType) (p t s:R) (a b : \bar R):
  (0<p)%R ->(0<t)%R ->(0<=s)%R ->0<=a ->0<=b ->
  (t^-1<=s)%R ->(s<=t)%R ->a<=p%:E*b ->b<=p%:E*a ->
  a*s%:E<=(p* t)%R%:E*b /\ b<=(p* t)%R%:E*(a*s%:E).
Proof.
move=>hp ht hs ha hb hSL hSU hAB hBA.
have hSLift:t^-1%:E<=s%:E by rewrite lee_fin.
have hSULift:s%:E<=t%:E by rewrite lee_fin.
have hsE:0<=s%:E by rewrite lee_fin.
have hpE:0<=p%:E by rewrite lee_fin; exact:ltW hp.
have htE:0<=t%:E by rewrite lee_fin; exact:ltW ht.
have htNe:t!=0%R by rewrite(gt_eqF ht).
have hUnit:1<=t%:E*s%:E.
  have hh:=ler_wpM2l (ltW ht) hSL.
  rewrite (mulfV htNe) in hh; by rewrite -EFinM lee_fin.
have hBack:a<=t%:E*(a*s%:E).
  have hh:=lee_wpmul2r ha hUnit.
  rewrite mul1e in hh.
  have hEq:(t%:E*s%:E)*a=t%:E*(a*s%:E) by rewrite -muleA [s%:E*a]muleC.
  by rewrite hEq in hh.
split.
- apply:(le_trans (lee_wpmul2l ha hSULift)).
  have hScaled:=lee_wpmul2r htE hAB.
  have hEq:(p%:E*b)*t%:E=(p* t)%R%:E*b.
    by rewrite muleAC -EFinM.
  by rewrite hEq in hScaled.
- apply:(le_trans hBA).
  have hh:=lee_wpmul2l hpE hBack.
  by rewrite muleA -EFinM in hh.
Qed.
