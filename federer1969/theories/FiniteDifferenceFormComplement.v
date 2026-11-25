(** Federer (1969), 3.4.5, p. 321: relative
    complement preserves the finite original difference form.
    Finite De Morgan expansion uses only unions and
    intersections of the original analytic varieties. *)
From mathcomp Require Import all_boot boolp classical_sets.
From Federer Require Import FiniteBooleanDifferenceUP FiniteDifferenceFormUnion FiniteDifferenceFormIntersection.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Section Complement.
Variable X:choiceType.
Variable U:set X.
Variable C:set (set X).
Hypothesis hEmpty:C set0.
Hypothesis hWhole:C U.
Hypothesis hUnion:forall S T,C S ->C T ->C (S `|` T).
Hypothesis hInter:forall S T,C S ->C T ->C (S `&` T).
Hypothesis hInside:forall S,C S ->S `<=` U.

(** Source for [finite_difference_form_base]: each original
    variety has a finite difference form, 3.4.5, p. 321. *)
Lemma finite_difference_form_base (S:set X):C S ->has_finite_difference_form C S.
Proof.
move=>hS;rewrite -(setD0 S);exact:finite_difference_form_pair hS hEmpty.
Qed.

(** Source for [finite_difference_form_inside]: every term
    and therefore the whole normal form lies in the
    original open domain U, 3.4.5, p. 321. *)
Lemma finite_difference_form_inside (A:set X):has_finite_difference_form C A ->A `<=` U.
Proof.
move=>[F [hF ->]];elim:F hF=>[|[S T] F ih] hF x /=;first by case.
move=>[[hx hnT]|hx].
- exact:hInside S (hF (S,T) (mem_head (S,T) F)).1 x hx.
- apply:(ih _ x hx)=>p hp;apply:hF;by rewrite in_cons hp orbT.
Qed.

(** Source for [relative_complement_of_difference]: the
    complement of one original variety difference is a
    two-term difference union, supporting 3.4.5, p. 321. *)
Lemma relative_complement_of_difference (S T:set X):T `<=` U ->
  U `\` (S `\` T)=(U `\` S) `|` T.
Proof.
move=>hTU;rewrite setDE setCD setIUr (setIidr hTU);reflexivity.
Qed.

(** Source for [finite_difference_form_complement]: relative
    complement in U preserves the exact original finite
    normal form, 3.4.5, p. 321. *)
Theorem finite_difference_form_complement (A:set X):
  has_finite_difference_form C A ->has_finite_difference_form C (U `\` A).
Proof.
move=>[F [hF ->]];elim:F hF=>[|[S T] F ih] hF.
- rewrite /= setD0;exact:finite_difference_form_base hWhole.
- have [hS hT]:=hF (S,T) (mem_head (S,T) F).
  have hTail p (hp:p \in F):C p.1 /\C p.2.
    apply:hF;by rewrite in_cons hp orbT.
  rewrite /= setDUr (@relative_complement_of_difference S T (@hInside T hT)).
  apply:(@finite_difference_form_intersection X C hUnion hInter).
  + apply:finite_difference_form_union.
    * exact:finite_difference_form_pair hWhole hS.
    * exact:finite_difference_form_base hT.
  + exact:ih hTail.
Qed.
End Complement.
