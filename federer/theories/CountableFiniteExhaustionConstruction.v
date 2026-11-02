(** Private finite-exhaustion construction supporting Federer (1969), 2.4.8,
    p. 84. An injection of the countable indexing set into the natural
    numbers supplies finite inverse images of initial segments. No
    surjectivity, nonempty index set, or repeated enumeration is assumed.
    Source context: CountableFiniteExhaustionUP.v. *)
From mathcomp Require Import all_boot finmap boolp classical_sets cardinality.
From Federer Require Import CountableFiniteExhaustionUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope fset_scope.
Local Open Scope classical_set_scope.

(** Source for [countable_finite_exhaustion_exists]: supporting
    existence of the finite exhaustion used to deduce Federer
    2.4.8 from 2.4.7, p. 84. *)
Theorem countable_finite_exhaustion_exists (J : choiceType) (D : set J) :
  countable D -> exists C, is_countable_finite_exhaustion D C.
Proof.
move=> /countable_injP[g hg].
pose E n := D `&` [set j | (g j < n)%N].
have hE n : finite_set (E n).
  have hgi : {in E n &, injective g}.
    move=> i j /set_mem[hi _] /set_mem[hj _] he.
    exact: hg (mem_set hi) (mem_set hj) he.
  rewrite -(eq_finite_set (inj_card_eq hgi)).
  apply: (@sub_finite_set nat (g @` E n) `I_n _ (finite_II n)).
  by move=> k [j [_ hj] <-].
pose C n := fset_set (E n).
have hC n j : j \in C n <-> E n j.
  rewrite /C (in_fset_set (hE n)); split; [exact: set_mem|exact: mem_set].
exists C; constructor.
- apply/fsetP=> j; rewrite in_fset0; apply/negP=> hj.
  have hfalse : (g j < 0)%N := ((hC 0%N j).1 hj).2.
  by move: hfalse; rewrite ltn0.
- move=> n j hj; exact: ((hC n j).1 hj).1.
- move=> n m hnm; apply/fsubsetP=> j hj.
  have [hD hgN] := (hC n j).1 hj; apply: (hC m j).2; split=> //.
  exact: leq_trans hgN hnm.
- move=> j hj; exists (g j).+1; apply: (hC _ j).2; split=> //; exact: ltnSn.
Qed.
