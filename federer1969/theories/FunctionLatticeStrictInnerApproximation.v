(** Federer (1969), 2.5.3, pp. 94–95: inner approximation by lattice levels.
    This supporting argument is for F0, before passing to F1 and arbitrary
    finite measurable sets. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal.
From Federer Require Import FunctionLatticeUP FunctionLatticeLevelFamilies FunctionLatticeInnerLevels
  FunctionLatticeClosedLevelNormalization RepresentedLatticeClosedLevels RealIntegralFunctionalUP
  RealLatticeTruncationLimits ExtendedRealReciprocalBounds ExtendedRealLimitBounds
  MeasureUP MeasureContinuityBelow.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [represented_lattice_strict_inner_upper_bound]: Supporting
    Federer 2.5.3, p. 94. *)
Lemma represented_lattice_strict_inner_upper_bound (R : realType) (X : choiceType)
    (L : set (X -> R)) (A : (X -> R) -> R) (hL : is_function_lattice L)
    (mu : set X -> \bar R) (hm : is_measure mu) (hA : is_real_integral_functional mu L A)
    (V : set X) (b : \bar R) :
  function_lattice_strict_levels L V ->
  (forall a, function_lattice_inner_unit_values L mu V a -> a <= b) -> mu V <= b.
Proof.
move=> [f [t [hf [ht ->]]]] hb.
pose u n := (t+((n.+1)%:R)^-1)%R.
pose C n := [set x | (u n <= f x)%R].
have hu n : (t < u n)%R by rewrite /u ltrDl invr_gt0 ltr0n.
have hupos n : (0 < u n)%R := lt_trans ht (hu n).
have hC n := @represented_lattice_closed_upper_level_measurable R X L A mu hm hA f (u n) hf.1.
have hmono n m : (n <= m)%N -> C n `<=` C m.
  move=> hnm x hx; apply: le_trans _ hx; rewrite /u lerD2l.
  exact: (@positive_reciprocal_nat_antitone R n m hnm).
have hunion : (\bigcup_n C n)=[set x | (t < f x)%R].
  apply/seteqP; split=> x.
  - move=> [n _ hn]; exact: lt_le_trans (hu n) hn.
  - move=> hx; have hgap : (0 < f x-t)%R by rewrite subr_gt0.
    have [n hn] := positive_reciprocal_nat_small hgap.
    exists n=> //; change (is_true ((t+((n.+1)%:R)^-1 <= f x)%R)).
    apply: ltW; by move: hn; rewrite ltrBrDl addrC.
have hlim := @measure_continuity_below R X mu hm C hC hmono.
rewrite -hunion; apply: (extended_order_limit_upper_bound hlim.2)=> n.
have [h [hh heq]] := @positive_lattice_closed_level_normalise R X L hL f (u n) hf (hupos n).
apply: hb; exists h; split=> //; split.
- move=> x hx; have hfx : (u n <= f x)%R.
    have he : C n=[set x | (1 <= h x)%R] := heq.
    by rewrite -he in hx.
  exact: lt_le_trans (hu n) hfx.
- exact: (congr1 mu heq).
Qed.
