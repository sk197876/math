(** Federer (1969), proof of 2.5.2, p. 92: the suiting-sequence envelope is
    a measure. The nonempty lattice is required here; the empty-lattice
    representation is handled separately. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets cardinality reals constructive_ereal.
From Federer Require Import FunctionLatticeUP FunctionLatticeLaws MonotoneDaniellIntegralUP
  DaniellCoverUP DaniellCoverBasic DaniellDiagonalCover NonnegativeSum NonnegativeSumAdd
  CountableGeometricBudget MeasureUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [daniell_cover_is_measure]: the measure assertion for the
    constructed phi in Federer 2.5.2, p. 92 This proves all countable
    covering inequalities, including the empty cover. *)
Theorem daniell_cover_is_measure (R : realType) (X : choiceType)
    (L : set (X -> R)) (A : (X -> R) -> R) (hL : is_function_lattice L)
    (hA : is_monotone_daniell_integral L A) (mu : set X -> \bar R)
    (hm : is_daniell_cover_envelope L A mu) : L (fun _ => 0%R) -> is_measure mu.
Proof.
move=> h0; constructor; first exact: (@daniell_cover_nonnegative R X L A hL hA mu hm).
move=> T F hF hT.
have hsum0 : 0 <= nonnegative_sum F mu := nonnegative_sum_nonnegative F mu.
case hs: (nonnegative_sum F mu)=> [r| |]; last by move: hsum0; rewrite hs.
2: exact: leey.
apply/lee_addgt0Pr=> e he.
have [b [hb hbsum]] := @countable_geometric_error_budget R (set X) F e hF he.
have happ B : exists fc : (nat -> X -> R) * \bar R,
    F B -> is_daniell_suiting_sequence L B fc.1 /\
      is_daniell_sequence_cost A fc.1 fc.2 /\ fc.2 < mu B + (b B)%:E.
  case: (pselect (F B))=> hB; last by exists ((fun _ _ => 0%R), 0).
  have hlt : mu B < +oo.
    apply: le_lt_trans (@nonnegative_sum_term R (set X) F mu B hB) _.
    by rewrite hs ltry.
  have hfin : mu B \is a fin_num.
    have hnon := @daniell_cover_nonnegative R X L A hL hA mu hm B.
    by rewrite ge0_fin_numE.
  have hap : mu B < mu B + (b B)%:E.
    by rewrite -(fineK hfin) -EFinD lte_fin ltrDl hb.
  have [f [c hc]] := daniell_cover_approximation hm hap.
  by exists (f,c).
pose fc B := projT1 (cid (happ B)).
have hfc B : F B -> is_daniell_suiting_sequence L B (fc B).1 /\
    is_daniell_sequence_cost A (fc B).1 (fc B).2 /\ (fc B).2 < mu B + (b B)%:E :=
  projT2 (cid (happ B)).
have hf B (hB : F B) := (hfc B hB).1.
have hc B (hB : F B) := (hfc B hB).2.1.
have hd := @daniell_cover_countable_suiting_bound R X (set X) L A hL hA mu hm F
  (fun B => B) T (fun B => (fc B).1) (fun B => (fc B).2) h0 hF hT hf hc.
apply: le_trans hd _.
have hmono : nonnegative_sum F (fun B => (fc B).2) <=
    nonnegative_sum F (fun B => mu B + (b B)%:E).
  apply: nonnegative_sum_mono=> B hB; exact: ltW (hfc B hB).2.2.
apply: le_trans hmono _.
have hmu B (hB : F B) : 0 <= mu B := @daniell_cover_nonnegative R X L A hL hA mu hm B.
have hb0 B (hB : F B) : 0 <= (b B)%:E := ltW (hb B).
rewrite (@nonnegative_sum_add R (set X) F mu (fun B => (b B)%:E) hmu hb0) hs.
apply: leeD (lexx _) _.
apply: le_trans hbsum _; rewrite lee_fin ler_pdivrMr ?ltr0n // mulr_natr.
by rewrite lerDl; exact: ltW he.
Qed.
