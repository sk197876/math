(** Federer (1969), 2.1.2, pp. 53–54, supporting
    3.3.19, p. 305: normalized finite outer-measure
    bounds retain the original sets in a binary cover. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal lra.
From Federer Require Import MeasureUP MeasureBasic MeasureSplit.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section Remainder.
Variable R:realType.
Variable X:choiceType.
Variable mu:set X->\bar R.
Hypothesis hMu:is_measure mu.

(** Source for [normalized_binary_measure_remainder]: if an
    actual original test T is covered by C union D, a
    normalized lower bound L for T and upper bound U for D
    give the normalized lower bound L-U for C. Finite C
    justifies extended-real cancellation. This expands the
    cap subtraction in 3.3.19, p. 305 using 2.1.2. *)
Theorem normalized_binary_measure_remainder (T C D:set X) (d L U:R):
  0<d ->(mu C< +oo)%E ->T `<=` C `|` D ->
  (L%:E<=mu T/d%:E)%E ->(mu D/d%:E<=U%:E)%E ->
  ((L-U)%:E<=mu C/d%:E)%E.
Proof.
move=>hd hCF hCover hLower hUpper.
have hCN:mu C \is a fin_num.
  rewrite ge0_fin_numE;last exact:measure_nonnegative hMu C.
  exact:hCF.
have hdN:d!=0 by rewrite gt_eqF.
have hInverse:((0:R)%:E<=(d%:E)^-1)%E by rewrite inver (gt_eqF hd) lee_fin invr_ge0;exact:ltW hd.
have hInverseFinite:((d%:E)^-1)%E \is a fin_num by rewrite inver (gt_eqF hd).
have hNormalizedFinite:(mu C/d%:E)%E \is a fin_num:= fin_numM hCN hInverseFinite.
have hBinary:= @measure_binary_cover R X mu hMu T C D hCover.
have hNormalized:= lee_wpmul2r hInverse hBinary.
have hAdd:((mu C+mu D)*(d%:E)^-1= mu C/d%:E+mu D/d%:E)%E.
  apply:muleDl=>//.
  exact:(@ge0_adde_def R (mu C) (mu D) (measure_nonnegative hMu C) (measure_nonnegative hMu D)).
rewrite hAdd in hNormalized.
have hComparison:= le_trans hLower (le_trans hNormalized (leeD2l (mu C/d%:E)%E hUpper)).
by rewrite EFinB lee_subel_addr //.
Qed.
End Remainder.
