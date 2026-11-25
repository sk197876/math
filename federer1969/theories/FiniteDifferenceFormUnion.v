(** Federer (1969), 3.4.5, p. 321: elementary
    finite difference normal forms, and closure under union. *)
From mathcomp Require Import all_boot boolp classical_sets.
From Federer Require Import FiniteBooleanDifferenceUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Section Forms.
Variable X:choiceType.
Variable C:set (set X).

(** Source for [finite_difference_union_cat]: concatenation
    preserves the original finite union of differences,
    supporting 3.4.5, p. 321. *)
Lemma finite_difference_union_cat (F G:seq (set X*set X)):
  finite_difference_union (F++G)=finite_difference_union F `|` finite_difference_union G.
Proof. by elim:F=>[|[S T] F ih] /=;[rewrite set0U|rewrite ih setUA]. Qed.

(** Source for [finite_difference_form_empty]: the empty
    set has the empty finite normal form, 3.4.5, p. 321. *)
Lemma finite_difference_form_empty:has_finite_difference_form C set0.
Proof. exists [::];split;last reflexivity. by move=>p;rewrite in_nil. Qed.

(** Source for [finite_difference_form_pair]: a difference
    of two original sets has the one-pair normal form,
    3.4.5, p. 321. *)
Lemma finite_difference_form_pair (S T:set X):C S ->C T ->has_finite_difference_form C (S `\` T).
Proof.
move=>hS hT;exists [::(S,T)];split.
- move=>p;rewrite in_cons in_nil orbF=>/eqP ->;by split.
- by rewrite /= setU0.
Qed.

(** Source for [finite_difference_form_union]: finite union
    preserves the original difference normal form,
    3.4.5, p. 321. *)
Lemma finite_difference_form_union (S T:set X):
  has_finite_difference_form C S ->has_finite_difference_form C T ->has_finite_difference_form C (S `|` T).
Proof.
move=>[F [hF ->]] [G [hG ->]];exists (F++G);split.
- move=>p;rewrite mem_cat=>/orP [hp|hp];[exact:hF p hp|exact:hG p hp].
- exact:esym (finite_difference_union_cat F G).
Qed.
End Forms.
