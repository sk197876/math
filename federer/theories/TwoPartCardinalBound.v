(** Finite cardinal arithmetic for Federer (1969), 2.8.11, pp. 147–148: P is
    the union of its distinguished pair and two parts each of cardinality at
    most zeta. This is supporting set theory; no geometric hypothesis is
    encoded in this lemma. *)
From mathcomp Require Import all_boot all_order finmap boolp
  classical_sets cardinality.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Local Open Scope card_scope.

(** Source for [two_part_cardinal_bound]: the concluding
    card P<=2 zeta+1 in Federer 2.8.11, pp. 147–148.
    It suffices that P be covered by two zeta-bounded sets and
    one point. Finiteness of the two parts follows from their
    cardinal bounds and is not an extra assumption. *)
Lemma two_part_cardinal_bound (T : choiceType) (P B C : set T)
    (p : T) (zeta : nat) :
  P `<=` [set p] `|` (B `|` C) ->
  B #<= [set: 'I_zeta] -> C #<= [set: 'I_zeta] ->
  P #<= [set: 'I_(2*zeta+1)].
Proof.
move=> hP hB hC.
have hBi : B #<= `I_zeta by rewrite (card_le_eqr (@card_II zeta)).
have hCi : C #<= `I_zeta by rewrite (card_le_eqr (@card_II zeta)).
have hBf : finite_set B := card_le_finite hB (@finite_finset _ (@setT 'I_zeta)).
have hCf : finite_set C := card_le_finite hC (@finite_finset _ (@setT 'I_zeta)).
pose U := [set p] `|` (B `|` C).
have hBCf : finite_set (B `|` C) by rewrite finite_setU; split.
have hUf : finite_set U.
  rewrite /U finite_setU; split; [exact: finite_set1|exact hBCf].
have hUB : (#|` fset_set B| <= zeta)%N := geq_card_fset_set hBi.
have hUC : (#|` fset_set C| <= zeta)%N := geq_card_fset_set hCi.
have hsize : (#|` fset_set U| <= 2*zeta+1)%N.
  rewrite /U !fset_setU ?finite_set1 ?finite_setU // fset_set1.
  have h1 : (#|` ([fset p] `|` (fset_set B `|` fset_set C))%fset| <=
      #|` ([fset p]%fset)| + #|` (fset_set B `|` fset_set C)%fset|)%N :=
    (leq_card_fsetU _ _).1.
  have h2 : (#|` (fset_set B `|` fset_set C)%fset| <= #|` fset_set B| + #|` fset_set C|)%N :=
    (leq_card_fsetU _ _).1.
  apply: leq_trans h1 _; apply: leq_trans (leq_add (leqnn _) h2) _.
  rewrite cardfs1 mul2n -addnn addnC.
  exact: leq_add (leq_add hUB hUC) (leqnn 1).
have [m hm] := (finite_setP _).1 hUf.
have hUm : (#|` fset_set U| = m) := card_fset_set hm.
have hUbound : U #<= [set: 'I_(2*zeta+1)].
  rewrite (card_le_eql hm) -(card_le_eqr (@card_II (2*zeta+1))) card_le_II.
  by rewrite -hUm.
exact: card_le_trans (subset_card_le hP) hUbound.
Qed.
