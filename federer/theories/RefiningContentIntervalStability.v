(** Federer (1969), 2.10.47, p. 205: apply step (2) repeatedly to identify
    every earlier content of a retained compact set with its last content.
    This finite induction uses only the abstract covering laws and local
    cost bounds. Source context: RefiningContentStability.v. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal.
From Federer Require Import RefiningCoverContent RefiningContentStability.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [refining_content_shifted_interval_stability]:
    the equality gamma_i(E_j)=gamma_j(E_j) in
    2.10.47, p. 205, with h added to
    the zero-based indices of the retained sequence. *)
Theorem refining_content_shifted_interval_stability (R : realType) (X : choiceType)
    H cost (gamma : nat -> set X -> \bar R) h k j (E : set X) :
  (forall i, is_refining_cover_content H cost i (gamma i)) ->
  (forall S, 0<=cost S) -> (k<=j)%N ->
  (forall u, (k<=u<j)%N -> forall S, H (h+u)%N S ->
    gamma (h+u).+1 (S `&` E)<=cost S) -> gamma (h+k)%N E=gamma (h+j)%N E.
Proof.
move=> hg hc; elim: j=> [|j IH] hkj hlocal.
- have -> : k=0%N by move: hkj; rewrite leqn0=>/eqP.
  reflexivity.
- case: (eqVneq k j.+1)=> [->|hkne]; first reflexivity.
  have hkj' : (k<=j)%N by move: hkj; rewrite leq_eqVlt (negPf hkne) /= ltnS.
  rewrite (IH hkj').
  2: move=> u /andP [hku huj] S hS; apply: hlocal hS.
  2: by apply/andP; split=> //; exact: ltn_trans huj (ltnSn j).
  rewrite addnS; symmetry.
  apply: (@refining_content_successor_stability R X H cost (h+j)%N
    (gamma (h+j)%N) (gamma (h+j).+1) E (hg _) (hg _) (fun S _=>hc S))=> S hS.
  apply: hlocal hS; by rewrite hkj' ltnSn.
Qed.
