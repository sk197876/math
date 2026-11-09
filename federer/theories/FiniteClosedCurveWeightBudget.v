(** Federer (1969), 3.3.19, p. 304:
    ordering finitely many actual boundary parameters
    is an existence proof for the complete cyclic
    sum. No boundary order is supplied as a hypothesis. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology.
From Federer Require Import CurveVariationUP ClosedCurveWeightBudget.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [finite_closed_curve_weight_budget]:
    the finite boundary sum in 3.3.19, p. 304,
    with the ordering discharged by sorting the actual
    finite family of real parameters. The distance
    budget is for distinct original labels; all
    endpoint weights are counted exactly twice. *)
Theorem finite_closed_curve_weight_budget (R:realType) (Y:metricType R)
    (I:finType) (g:R->Y) (t:I->R) (w:I->R) (a b:R):
  (2<=#|I|)%N ->
  (forall i,a<=t i /\t i<=b) ->g a=g b ->
  (forall i j,i!=j ->w i+w j<=mdist (g (t i)) (g (t j))) ->
  ((2*(\sum_i w i))%:E<=curve_variation g a b)%E.
Proof.
move=>hCard hBounds hEnds hPair.
pose order:=fun i j:I=>t i<=t j.
pose s:=sort order (enum I).
have hUnique:uniq s by rewrite /s sort_uniq enum_uniq.
have hSorted:sorted <=%O (map t s).
  rewrite sorted_map;apply:sort_sorted=>i j;exact:le_total.
have hSize:(2<=size s)%N by rewrite /s size_sort -cardE.
have hSum:(\sum_(i<-s) w i)=\sum_i w i.
  have hPerm:perm_eq s (enum I).
    apply:uniq_perm;first exact hUnique.
    - exact:enum_uniq.
    - by move=>i;rewrite /s mem_sort mem_enum.
  rewrite -big_enum;exact:perm_big hPerm.
case hShape:s hUnique hSorted hSize hSum=>[|i [|j rest]] hUnique hSorted hSize hSum.
- by move:hSize.
- by move:hSize.
- rewrite -hSum.
  exact:(@closed_curve_ordered_weight_budget R Y I g t w a b i j rest hUnique hSorted
    (fun k _=>hBounds k) hEnds (fun k l _ _=>hPair k l)).
Qed.
