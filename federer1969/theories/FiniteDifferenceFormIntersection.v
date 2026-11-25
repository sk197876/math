(** Federer (1969), 3.4.5, p. 321: intersection
    preserves finite unions of original variety differences.
    Distribute finite unions and combine one pair of terms. *)
From mathcomp Require Import all_boot boolp classical_sets.
From Federer Require Import FiniteBooleanDifferenceUP FiniteDifferenceFormUnion.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [two_set_differences_intersection]: the
    original finite-term normal-form identity supporting
    3.4.5, p. 321. *)
Lemma two_set_differences_intersection (X:Type) (S T U V:set X):
  (S `\` T) `&` (U `\` V)=(S `&` U) `\` (T `|` V).
Proof.
apply/seteqP;split.
- move=>x [[hs hnT] [hu hnV]];split;first by split.
  by move=>[ht|hv];[exact:hnT ht|exact:hnV hv].
- move=>x [[hs hu] hnUnion];split.
  + split;first exact:hs. move=>ht;apply:hnUnion;by left.
  + split;first exact:hu. move=>hv;apply:hnUnion;by right.
Qed.

Section Intersection.
Variable X:choiceType.
Variable C:set (set X).
Hypothesis hUnion:forall S T,C S ->C T ->C (S `|` T).
Hypothesis hInter:forall S T,C S ->C T ->C (S `&` T).

(** Source for [finite_difference_pair_intersection_form]:
    a single original difference intersected with a finite
    difference union has the same form, 3.4.5, p. 321. *)
Lemma finite_difference_pair_intersection_form (S T:set X) (G:seq (set X*set X)):
  C S ->C T ->(forall p,p \in G ->C p.1 /\C p.2) ->
  has_finite_difference_form C ((S `\` T) `&` finite_difference_union G).
Proof.
move=>hS hT;elim:G=>[|[U V] G ih] hG.
- rewrite /= setI0;exact:finite_difference_form_empty.
- have [hU hV]:=hG (U,V) (mem_head (U,V) G).
  have hTail p (hp:p \in G):C p.1 /\C p.2.
    apply:hG;by rewrite in_cons hp orbT.
  rewrite /= setIUr two_set_differences_intersection.
  apply:finite_difference_form_union;last exact:ih hTail.
  apply:finite_difference_form_pair;[exact:hInter S U hS hU|exact:hUnion T V hT hV].
Qed.

(** Source for [finite_difference_form_intersection]: arbitrary
    finite normal forms are closed under intersection,
    as required by 3.4.5, p. 321. *)
Theorem finite_difference_form_intersection (S T:set X):
  has_finite_difference_form C S ->has_finite_difference_form C T ->
  has_finite_difference_form C (S `&` T).
Proof.
move=>[F [hF ->]] [G [hG ->]].
elim:F hF=>[|[U V] F ih] hF.
- rewrite /= set0I;exact:finite_difference_form_empty.
- have [hU hV]:=hF (U,V) (mem_head (U,V) F).
  have hTail p (hp:p \in F):C p.1 /\C p.2.
    apply:hF;by rewrite in_cons hp orbT.
  rewrite /= setIUl;apply:finite_difference_form_union;last exact:ih hTail.
  exact:finite_difference_pair_intersection_form hU hV hG.
Qed.
End Intersection.
