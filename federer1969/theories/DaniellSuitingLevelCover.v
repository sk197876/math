(** Federer (1969), 2.5.3, pp. 94–95: level unions of sequences suiting a
    set provide outer approximations. This supporting lemma isolates that
    step using any representing measure. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal.
From Federer Require Import FunctionLatticeUP FunctionLatticeLevelFamilies FunctionLatticeLevelMeasurability
  DaniellCoverUP RealIntegralFunctionalUP MeasureUP MeasureContinuityBelow ExtendedRealLimitBounds.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [daniell_suiting_strict_level_cover]: increasing level union
    in the regularity proof of Federer 2.5.3, pp. 94–95 A real bound q for
    the functional values gives measure at most q/t. The threshold is
    strictly between zero and one. *)
Lemma daniell_suiting_strict_level_cover (R : realType) (X : choiceType)
    (L : set (X -> R)) (A : (X -> R) -> R) (mu : set X -> \bar R)
    (hm : is_measure mu) (hA : is_real_integral_functional mu L A)
    (S : set X) (f : nat -> X -> R) (q t : R) :
  is_daniell_suiting_sequence L S f -> (forall n, (A (f n) <= q)%R) ->
  (0 < t)%R -> (t < 1)%R -> exists V,
    S `<=` V /\ function_lattice_increasing_levels L V /\ mu V <= (q/t)%R%:E.
Proof.
move=> hf hq ht ht1.
pose V n := [set x | (t < f n x)%R].
have hV n : function_lattice_strict_levels L (V n).
  exists (f n),t; split; first exact: hf.1 n.
  by split.
have hmono n m : (n <= m)%N -> V n `<=` V m.
  move=> hnm x hx; exact: lt_le_trans hx (hf.2.1 n m hnm x).
have hmeas n := @represented_lattice_strict_level_measurable R X L A mu hm hA (V n) (hV n).
exists (\bigcup_n V n); split.
- move=> x hx; have [n hn] := hf.2.2 x hx t ht1; by exists n.
- split.
  + exists V; by split=> //; split.
  + have hlim := @measure_continuity_below R X mu hm V hmeas hmono.
    apply: (extended_order_limit_upper_bound hlim.2)=> n.
    have hb := @represented_lattice_strict_level_bound R X L A mu hm hA (f n) t (hf.1 n) ht.
    rewrite EFinM (@lee_pdivlMr R t (mu (V n)) q%:E ht) muleC.
    apply: le_trans hb _; by rewrite lee_fin; exact: hq.
Qed.
