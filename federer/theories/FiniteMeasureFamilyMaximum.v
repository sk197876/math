(** Federer (1969), 3.2.14, p. 252:
    finite measure maximization on a nonempty class
    closed under countable unions. The bounded score
    and its monotonicity are proved from measure laws. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals constructive_ereal.
From Federer Require Import MeasureUP MeasureBasic CountableUnionFamilyMaximum.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [finite_measure_countable_union_maximum]:
    supporting maximization of phi restricted to A,
    Federer 3.2.14, p. 252. The class itself need
    not consist of measurable sets for attainment. *)
Theorem finite_measure_countable_union_maximum (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (C : set (set X)) :
  is_measure mu -> mu setT< +oo -> (exists A, C A) ->
  (forall F : nat -> set X, (forall n, C (F n)) -> C (\bigcup_n F n)) ->
  exists B, C B /\ forall A, C A -> mu A<=mu B.
Proof.
move=> hm hfin hex hU.
have hfinite A : mu A \is a fin_num.
  rewrite ge0_fin_numE; last exact: (@measure_nonnegative R X mu hm A).
  apply: le_lt_trans _ hfin; apply: (@measure_mono R X mu hm)=> x hx; exact I.
have hval A : mu A=(fine (mu A))%:E by rewrite fineK //; exact: hfinite.
pose r A := fine (mu A).
pose M := fine (mu setT).
have hb A : C A -> (0<=r A<=M)%R.
  move=> hA; apply/andP; split.
  - have hh := @measure_nonnegative R X mu hm A.
    by rewrite (hval A) lee_fin in hh.
  - have hh := @measure_mono R X mu hm A setT (fun x hx => I).
    by rewrite (hval A) (hval setT) lee_fin in hh.
have hmono A B : C A -> C B -> A `<=` B -> (r A<=r B)%R.
  move=> hA hB hAB; have hh := measure_mono hm hAB.
  by rewrite (hval A) (hval B) lee_fin in hh.
have [B [hB hmax]] := countable_union_family_maximum hex hb hU hmono.
exists B; split=> // A hA.
rewrite (hval A) (hval B) lee_fin; exact: hmax A hA.
Qed.
