(** Federer (1969), 2.5.8, p. 100: an L-infinity envelope for a countable
    sequence in the unit ball. Finite maxima and the already sealed
    lower-limit construction give a real representative of the countable
    supremum on a conull set. This avoids choosing separate bounded
    representatives; the corrected null-norm hypothesis makes the almost
    domination sufficient. Compare erratum p. 2, book p. 100 lines 3, 7 and
    9. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal.
From Federer Require Import MeasureUP MeasureAlmostUP MeasureAlmostBasic FunctionLatticeUP FunctionLatticeLaws
  VectorFunctionLattice TotalScalarLpUP TotalScalarLpLattice TotalScalarLpIncreasingLimit
  IncreasingAbsoluteMaximum TotalEssentialNormBound RealLowerLimitReplacement.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [total_scalar_lp_absolute]: supporting absolute-value closure
    for the envelope in Federer 2.5.8, p. 100 It holds at all Lp exponents. *)
Lemma total_scalar_lp_absolute (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu) p (f : X -> R) :
  total_scalar_lp mu p f -> total_scalar_lp mu p (fun x => `|f x|%R).
Proof.
move=> hf; have hL := @total_scalar_lp_vector_lattice R X mu hm p hf.1.
have hn := @vector_function_lattice_negation R X _ hL f hf.
have hh := @function_lattice_maximum R X _ hL.1 f (fun x => (-f x)%R) hf hn.
have he : (fun x => Order.max (f x) (-f x)%R)=(fun x => `|f x|%R).
  apply: funext=> x; apply/eqP; rewrite eq_le; apply/andP; split.
  - rewrite ge_max ler_norm; have hb := ler_norm (-f x); by rewrite normrN in hb.
  - case: (leP 0%R (f x))=> h.
    + by rewrite (ger0_norm h) le_max lexx.
    + by rewrite (ler0_norm (ltW h)) le_max lexx orbT.
by rewrite he in hh.
Qed.

(** Source for [linfinity_sequence_has_upper_envelope]: the countable
    supremum step in Federer 2.5.8, p. 100 The conclusion retains full
    L-infinity membership, including countably measurable support. *)
Theorem linfinity_sequence_has_upper_envelope (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu) (f : nat -> X -> R) :
  (forall n, total_scalar_lp mu +oo (f n)) ->
  (forall n, total_scalar_lp_norm mu +oo (f n) <= 1) ->
  exists g : X -> R, total_scalar_lp mu +oo g /\ (forall x, (0 <= g x)%R) /\
    total_scalar_lp_norm mu +oo g <= 1 /\
    forall n, measure_almost_everywhere mu [set x | (`|f n x| <= g x)%R].
Proof.
move=> hf hb; pose u := increasing_absolute_maximum f.
have hL := (@total_scalar_lp_vector_lattice R X mu hm +oo (leey _)).1.
have hu n : total_scalar_lp mu +oo (u n).
  elim: n=> [|n ih]; first exact: (@total_scalar_lp_absolute R X mu hm +oo (f 0%N) (hf 0%N)).
  exact: (@function_lattice_maximum R X _ hL _ _ ih
    (@total_scalar_lp_absolute R X mu hm +oo (f n.+1) (hf n.+1))).
have hu0 := @increasing_absolute_maximum_nonnegative R X f.
have hinc := @increasing_absolute_maximum_increases R X f.
have hau n : measure_almost_everywhere mu [set x | (u n x <= 1)%R].
  elim: n=> [|n ih].
  - exact: (@total_essential_norm_almost_bound R X mu hm (f 0%N) 1%R (hf 0%N) (hb 0%N)).
  - have ha := @total_essential_norm_almost_bound R X mu hm (f n.+1) 1%R (hf n.+1) (hb n.+1).
    apply: (@measure_almost_everywhere_mono R X mu hm _ _ _
      (@measure_almost_everywhere_and R X mu hm _ _ ih ha))=> x [hx hy].
    change (is_true (Order.max (u n x) `|f n.+1 x|%R <= 1)%R).
    by rewrite ge_max hx hy.
have hub n : total_scalar_lp_norm mu +oo (u n) <= 1.
  apply: (@total_essential_norm_bound R X mu hm (u n) 1%R (ler01)).
  apply: (@measure_almost_everywhere_mono R X mu hm _ _ _ (hau n))=> x hx.
  change (is_true (`|u n x| <= 1)%R); by rewrite (ger0_norm (hu0 n x)).
have [hg [hg0 [hgn hconv]]] := @bounded_increasing_lp_replacement R X mu hm +oo 1%R u hu hu0 hinc hub.
have hupper := @bounded_increasing_lp_upper_representative R X mu hm +oo 1%R u hu hu0 hinc hub.
exists (real_lower_limit_replacement u); split=> //; split=> //; split=> // n.
apply: (@measure_almost_everywhere_mono R X mu hm _ _ _ hupper)=> x hx.
exact: le_trans (@increasing_absolute_maximum_diagonal R X f n x) (hx n).
Qed.
