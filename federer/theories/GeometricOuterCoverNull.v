(** Federer (1969), 3.3.19, p. 305: the exceptional
    set avoiding an original proper arc has outer mass zero
    once its finite-stage masses contract geometrically. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal.
From Federer Require Import MeasureUP MeasureBasic GeometricUniformTail ExtendedRealOrderTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [geometric_outer_cover_null]: supporting the
    vanishing exceptional intersection in 3.3.19, p. 305.
    The original exceptional set and covering stages need not
    be measurable. Actual outer monotonicity and a vanishing
    finite geometric budget suffice. *)
Theorem geometric_outer_cover_null (R:realType) (X:choiceType)
    (mu:set X-> \bar R) (B:set X) (F:nat->set X) (q M:R):
  is_measure mu ->0<q<1 ->0<=M ->
  (forall n,B `<=` F n) ->
  (forall n,(mu (F n)<=(q^+n*M)%:E)%E) ->mu B=0%E.
Proof.
move=>hMu hq hM hCover hBound.
apply/eqP;rewrite eq_le (measure_nonnegative hMu B) andbT.
rewrite leNgt;apply/negP=>hPositive.
have [t [ht0 htB]]:=@extended_rationals_order_dense R 0 (mu B) hPositive.
have htReal:(0<ratr t:>R) by move:ht0;rewrite lte_fin.
have [N hSmall]:=@geometric_uniform_tail R q M (ratr t) hq hM htReal.
have hMass:=le_trans (@measure_mono R X mu hMu B (F N) (hCover N)) (hBound N).
have hStrict:((q^+N*M)%:E<(ratr t:R)%:E)%E.
  by rewrite lte_fin;exact:hSmall N (leqnn N).
have hContradiction:=le_lt_trans hMass (lt_trans hStrict htB).
by rewrite ltxx in hContradiction.
Qed.
