(** Federer (1969), 3.4.5, p. 321: finite
    Boolean operations give exactly finite unions of differences
    of original varieties. This supporting set-theoretic proof
    retains the original family and ambient open domain. *)
From mathcomp Require Import all_boot boolp classical_sets.
From Federer Require Import FiniteBooleanDifferenceUP FiniteDifferenceFormUnion
  FiniteDifferenceFormIntersection FiniteDifferenceFormComplement.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Section NormalForm.
Variable X:choiceType.
Variable U:set X.
Variable C:set (set X).
Hypothesis hEmpty:C set0.
Hypothesis hWhole:C U.
Hypothesis hUnion:forall S T,C S ->C T ->C (S `|` T).
Hypothesis hInter:forall S T,C S ->C T ->C (S `&` T).
Hypothesis hInside:forall S,C S ->S `<=` U.

(** Source for [finite_difference_form_difference]: the
    original finite normal forms are closed under set
    difference, 3.4.5, p. 321. *)
Lemma finite_difference_form_difference (S T:set X):
  has_finite_difference_form C S ->has_finite_difference_form C T ->has_finite_difference_form C (S `\` T).
Proof.
move=>hS hT.
have hSU:=@finite_difference_form_inside X U C hInside S hS.
have hEquation:S `\` T=S `&` (U `\` T).
  by rewrite !setDE setIA (setIidl hSU).
rewrite hEquation;apply:(@finite_difference_form_intersection X C hUnion hInter S (U `\` T) hS).
exact:(@finite_difference_form_complement X U C hEmpty hWhole hUnion hInter hInside T hT).
Qed.

(** Source for [finite_boolean_difference_normal_form]: the
    complete finite Boolean normal form asserted in
    3.4.5, p. 321. Both directions retain
    the original finite equation family and domain. *)
Theorem finite_boolean_difference_normal_form (A:set X):
  finite_boolean_set_closure C A <->has_finite_difference_form C A.

Proof.
split.
- elim=>[S hS|S T hS ihS hT ihT|S T hS ihS hT ihT|S T hS ihS hT ihT].
  + exact:(@finite_difference_form_base X C hEmpty S hS).
  + exact:finite_difference_form_union ihS ihT.
  + exact:(@finite_difference_form_intersection X C hUnion hInter S T ihS ihT).
  + exact:finite_difference_form_difference ihS ihT.
- move=>[F [hF ->]];elim:F hF=>[|[S T] F ih] hF.
  + exact:finite_boolean_base hEmpty.
  + have [hS hT]:=hF (S,T) (mem_head (S,T) F).
    apply:finite_boolean_union.
    * apply:finite_boolean_difference;[exact:finite_boolean_base hS|exact:finite_boolean_base hT].
    * apply:ih=>p hp;apply:hF;by rewrite in_cons hp orbT.
Qed.
End NormalForm.
