(** Federer (1969), 3.1.4, p. 216: estimate W=union_i S_i
    by the sum of the coordinate exceptional-set measures. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal.
From Federer Require Import MeasureUP MeasureBasic MeasureSplit.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [measure_finite_union_bound]: finite
    subadditivity used for W in Federer 3.1.4, p. 216.
    Neither the sets nor their union need be measurable. *)
Theorem measure_finite_union_bound (R : realType) (X : choiceType) (J : finType)
    (mu : set X -> \bar R) (S : J -> set X) :
  is_measure mu -> mu (\bigcup_j S j)<=\sum_j mu (S j).
Proof.
move=> hm.
have he : (\bigcup_j S j)=\big[setU/set0]_j S j.
  have hh := @bigcup_pred J _ xpredT S.
  have hset : [set j : J | xpredT j]=setT by apply/seteqP; split=> j _.
  by rewrite hset in hh.
rewrite he.
have hs : forall s : seq J, mu (\big[setU/set0]_(j<-s) S j)<=\sum_(j<-s) mu (S j).
  elim=> [|j s ih]; first by rewrite !big_nil (measure_empty hm).
  rewrite !big_cons; apply: le_trans (measure_binary_cover hm (fun x hx=>hx)) _.
  exact: leeD (lexx _) ih.
exact: hs.
Qed.
