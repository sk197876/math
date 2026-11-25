(** Federer (1969), 2.5.3, pp. 94–95: countably finite sets admit series of
    positive lattice functions. We apply the already proved finite-diagonal
    argument from 2.5.2 to sequences suiting the finite-measure covering
    sets. *)
From mathcomp Require Import all_boot all_order all_algebra finmap boolp classical_sets cardinality reals constructive_ereal.
From Federer Require Import FunctionLatticeUP FunctionLatticeLaws DaniellCoverUP DaniellCoverBasic
  DaniellDiagonalCover CountableFiniteExhaustionUP CountableFiniteExhaustionSealed
  LatticeSeriesCoverUP MeasureUP MeasureBasic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [countably_finite_set_daniell_suiting]: the countable-cover
    direction of Federer 2.5.3, p. 94, third condition, expanded to a
    suiting sequence The empty covering family is included using zero in the
    nonempty lattice. *)
Theorem countably_finite_set_daniell_suiting (R : realType) (X : choiceType)
    (L : set (X -> R)) (A : (X -> R) -> R) (hL : is_function_lattice L)
    (mu : set X -> \bar R) (hm : is_measure mu) (hc : is_daniell_cover_envelope L A mu)
    (T : set X) : L (fun _ => 0%R) -> is_countably_finite_measure_set mu T ->
  exists f, is_daniell_suiting_sequence L T f.
Proof.
move=> h0 [F [hF [hfin hT]]].
have happ B : exists f : nat -> X -> R, F B -> is_daniell_suiting_sequence L B f.
  case: (pselect (F B))=> hB; last by exists (fun _ _ => 0%R).
  have hfinite : mu B \is a fin_num.
    rewrite ge0_fin_numE; first exact: hfin B hB.
    exact: (@measure_nonnegative R X mu hm B).
  have hstrict : mu B < (fine (mu B)+1)%R%:E.
    by rewrite -{1}(fineK hfinite) lte_fin ltrDl ltr01.
  have [f [c [hf _]]] := daniell_cover_approximation hc hstrict.
  by exists f.
pose f B := projT1 (cid (happ B)).
have hf B : F B -> is_daniell_suiting_sequence L B (f B) := projT2 (cid (happ B)).
pose C := @CountableFiniteExhaustion.value (set X) F hF.
have hC := @CountableFiniteExhaustion.laws (set X) F hF.
exists (fun n x => (\sum_(B <- C n) f B n x)%R).
exact: (@daniell_diagonal_suits R X (set X) L hL F C hC (fun B => B) T f h0 hT hf).
Qed.
