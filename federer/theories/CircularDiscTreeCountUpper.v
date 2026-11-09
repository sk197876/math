(** Federer (1969), 3.3.19, p. 302: elementary upper
    counts before using actual disc separation. The original
    family may be covered with the full recursive budget;
    duplicate centres are never counted as distinct discs. *)
From mathcomp Require Import all_boot all_order all_algebra finmap reals.
From Federer Require Import EuclideanInnerProduct InnerMetric CircularDiscRefinement
  CircularDiscTreeUP FactorialDiscScalesUP FactorialDiscScalesSealed FiniteFsetUnionCardBound.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory.
Local Open Scope fset_scope.
Local Open Scope ring_scope.
Section Count.
Variable R:realType.
Local Notation E:=(inner_metric_space (@euclidean_inner_productP R 2)).

(** Source for [circular_disc_child_count_upper]: the
    n actual child indices give at most n distinct centres,
    supporting the cover budget of 3.3.19, p. 302. *)
Lemma circular_disc_child_count_upper (z:E) (r:R) n:
  (#|` [fset circular_disc_child_center z r k | k:'I_n]|<=n)%N.
Proof.
have hh:=leq_imfset_card imfset_key (fun k:'I_n=>circular_disc_child_center z r k)
  (mem_fin (fin_finpred (@predT 'I_n))).
rewrite /= -cardE card_ord in hh.
have hEq:[fset circular_disc_child_center z r k | k in (@predT 'I_n)]=
    [fset circular_disc_child_center z r k | k:'I_n].
  apply/fsetP=>x;apply/imfsetP/imfsetP.
  - move=>[k _ ->];by exists k.
  - move=>[k _ ->];by exists k.
by rewrite hEq in hh.

Qed.

(** Source for [circular_disc_refinement_count_upper]: each
    original parent contributes at most n actual children,
    supporting the level counts of 3.3.19, p. 302. *)
Lemma circular_disc_refinement_count_upper (H:{fset E}) r n:
  (#|` circular_disc_refinement H r n|<=#|` H|*n)%N.
Proof.
have hUpper:=@finite_fset_union_card_upper E E H
  (fun z=>[fset circular_disc_child_center z r k | k:'I_n]).
apply:leq_trans hUpper _.
have hSum:(\sum_(z<-H) #|` [fset circular_disc_child_center z r k | k:'I_n]|<=
    \sum_(z<-H) n)%N.
  apply:leq_sum=>z _;exact:circular_disc_child_count_upper.
apply:leq_trans hSum _.
by rewrite big_seq_fsetE sum_nat_const cardT cardfE cardE mulnC.
Qed.

(** Source for [circular_disc_tree_count_upper]: the original
    level has at most its specified factorial count, supporting
    the diameter sum in 3.3.19, p. 302. Exact equality is
    proved subsequently from actual geometric separation. *)
Lemma circular_disc_tree_count_upper (H:nat->{fset E}):
  is_circular_disc_tree H ->forall j,(#|` H j|<=@FactorialDiscScales.count R j)%N.
Proof.
move=>hH;elim=>[|j ih].
- by rewrite (circular_disc_tree_root hH) (factorial_disc_count_root (@FactorialDiscScales.laws R)) cardfs1.
- rewrite (circular_disc_tree_step hH) (factorial_disc_count_step (@FactorialDiscScales.laws R)).
  apply:leq_trans (circular_disc_refinement_count_upper _ _ _) _.
  rewrite mulnC;exact:leq_mul (leqnn _) ih.
Qed.
End Count.
