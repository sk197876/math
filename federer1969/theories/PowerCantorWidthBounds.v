(** Federer (1969), 3.3.21, p. 309: bounds and the exact original width recurrence. *)
From mathcomp Require Import all_boot all_order all_algebra boolp reals lra.
From Federer Require Import RealPower CantorSplitRadiusUP PowerCantorSplit PowerCantorWidthLawsUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [power_cantor_original_width_step]: the exact
    common original side w_(j+1)=w_j n_j^(-1/m), derived from
    the original Phi cost laws, supporting 3.3.21, p. 309. *)
Lemma power_cantor_original_width_step (R:realType) (c m:R) n w:
  0<c ->0<m ->(forall j,(2<=n j)%N) ->is_power_cantor_widths c m n w ->
  forall j,w j.+1=w j * real_power (n j)%:R (-m^-1).
Proof.
move=>hc hm hn hW j.
exact:(@power_cantor_split_length R c m (w j) (w j.+1) (n j) hc hm
  (power_cantor_width_positive hW j) (hn j) (power_cantor_width_split hW j)).
Qed.

(** Source for [power_cantor_original_width_decreases]: the actual
    common original widths decrease, supporting the separation scale
    and the cofinal small radii of 3.3.21, p. 309. *)
Lemma power_cantor_original_width_decreases (R:realType) (c m:R) n w:
  (forall j,(2<=n j)%N) ->is_power_cantor_widths c m n w ->
  forall j,w j.+1<=w j.
Proof.
move=>hn hW j.
have hw:=power_cantor_width_positive hW j.
have hN:1<((n j)%:R:R) by rewrite ltr1n;exact:hn j.
have hN0:0<((n j)%:R:R) by lra.
have hChild: w j.+1<w j/(n j)%:R:=(cantor_split_radius_bounds (power_cantor_width_split hW j)).2.
have hBound:w j/(n j)%:R<=w j by rewrite ler_pdivrMr //;nra.
exact:le_trans (ltW hChild) hBound.
Qed.

(** Source for [power_cantor_original_width_order]: every later
    original side is at most every earlier side, with unit-root
    upper bound, supporting all original levels of 3.3.21, p. 309. *)
Theorem power_cantor_original_width_order (R:realType) (c m:R) n w:
  (forall j,(2<=n j)%N) ->is_power_cantor_widths c m n w ->
  (forall j k,(j<=k)%N ->w k<=w j) /\forall j,w j<= 1.
Proof.
move=>hn hW.
have hStep:=power_cantor_original_width_decreases hn hW.
have hOrder j k:(j<=k)%N ->w k<=w j.
  elim: k=>[|k ih] hjk.
  - have ->:j=0%N by move:hjk;rewrite leqn0=>/eqP.
    exact:lexx.
  - case:(eqVneq j k.+1)=>[->|hDifferent];first exact:lexx.
    have hEarlier:(j<=k)%N.
      by move:hjk;rewrite leq_eqVlt (negbTE hDifferent) /= ltnS.
    exact:le_trans (hStep k) (ih hEarlier).
split;first exact:hOrder.
move=>j;have h:=hOrder 0%N j (leq0n j).
by rewrite (power_cantor_width_root hW) in h.
Qed.
