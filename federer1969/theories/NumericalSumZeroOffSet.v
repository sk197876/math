(** Federer (1969), 4.1.26, p. 383: passing
    from a zero-extended determinant-sign summand to
    the literal fibre intersected with A. This
    supporting identity is the original summation
    convention of 2.1.1(3)–(4), p. 52. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals constructive_ereal.
From Federer Require Import ExtendedRealPartial NonnegativeSum NonnegativeSumSupport
  NonnegativeSumRestriction NumericalSum NumericalSumValues.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [numerical_sum_zero_off_set]: deleting
    zero summands preserves the exact original
    partial signed sum, supporting the displayed
    formula of 4.1.26, p. 383. Undefined
    differences of infinite variations remain undefined. *)
Theorem numerical_sum_zero_off_set (R:realType) (X:choiceType)
    (D A:set X) (w:X->\bar R):
  (forall x,D x->~A x->w x=0)->
  numerical_sum D w=numerical_sum (D `&` A) w.
Proof.
move=>hOff;rewrite /numerical_sum.
have hPositive:nonnegative_sum D (fun x=>extended_positive_part (w x))=
    nonnegative_sum (D `&` A) (fun x=>extended_positive_part (w x)).
  rewrite -nonnegative_sum_restrict.
  apply:nonnegative_sum_ext=>x hx.
  case:(pselect (A x))=>hAx;first by rewrite (mem_set hAx).
  have hNot:x \notin A by apply/negP=>/set_mem h;exact:hAx h.
  by rewrite (negbTE hNot) (hOff x hx hAx) /extended_positive_part maxxx.
have hNegative:nonnegative_sum D (fun x=>extended_negative_part (w x))=
    nonnegative_sum (D `&` A) (fun x=>extended_negative_part (w x)).
  rewrite -nonnegative_sum_restrict.
  apply:nonnegative_sum_ext=>x hx.
  case:(pselect (A x))=>hAx;first by rewrite (mem_set hAx).
  have hNot:x \notin A by apply/negP=>/set_mem h;exact:hAx h.
  by rewrite (negbTE hNot) (hOff x hx hAx) /extended_negative_part oppe0
    /extended_positive_part maxxx.
by rewrite hPositive hNegative.
Qed.
