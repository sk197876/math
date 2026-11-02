(** Federer (1969), 3.2.3, p. 243: combine the
    determinant-scaled integral and image inequalities to obtain
    the factors lambda^(2m). All values may be infinite. *)
From mathcomp Require Import all_boot all_order all_algebra reals constructive_ereal.
From Federer Require Import ExtendedRealOrderTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope ereal_scope.

(** Source for [area_piece_scalar_bounds]: the displayed
    lambda^(2m) sandwich in Federer 3.2.3, p. 243,
    written equivalently as two upper comparisons. Positive
    finite factors cancel even when an integral is infinite. *)
Lemma area_piece_scalar_bounds (R:realType) (lambda:R) m (a b c : \bar R):
  (0<lambda)%R ->
  (lambda^-1^+m)%R%:E*c<=a -> a<=(lambda^+m)%R%:E*c ->
  b<=(lambda^+m)%R%:E*c -> c<=(lambda^+m)%R%:E*b ->
  a<=(lambda^+(m+m)%N)%R%:E*b /\ b<=(lambda^+(m+m)%N)%R%:E*a.
Proof.
move=>hl hLow hUp hImage hBack.
pose p:=(lambda^+m)%R.
pose q:=(lambda^-1^+m)%R.
have hp:(0<=p)%R:=exprn_ge0 m (ltW hl).
have hpE:0<=p%:E by rewrite lee_fin.
have hPQ:(p*q)%R= 1%R by rewrite /p /q -exprMn mulfV ?gt_eqF // expr1n.
have hCancel:c<=p%:E*a.
  have hh:=lee_wpmul2l hpE hLow.
  by rewrite muleA -EFinM hPQ mul1e in hh.
split.
- have hh:=le_trans hUp (lee_wpmul2l hpE hBack).
  by rewrite muleA -EFinM /p -exprD in hh.
- have hh:=le_trans hImage (lee_wpmul2l hpE hCancel).
  by rewrite muleA -EFinM /p -exprD in hh.
Qed.
