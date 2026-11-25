(** Federer (1969), 3.3.19, p. 303: elementary
    finite-set extraction behind the original first split.
    A finite family of cardinality at least two has
    two distinct actual members. *)
From mathcomp Require Import all_boot all_order finmap boolp.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope fset_scope.
Local Open Scope nat_scope.

(** Source for [finite_two_distinct_members]: supporting
    actual pair choice from a first-split hit family
    in 3.3.19, p. 303. Empty ambient
    types and arbitrary finite families are retained. *)
Theorem finite_two_distinct_members (I:choiceType) (F:{fset I}):
  2<=#|` F| ->exists z w:I,z \in F /\w \in F /\z!=w.
Proof.
move=>hCount.
case:(pselect (exists z,z \in F))=>[[z hz]|hNone];last first.
  have hF:F=fset0.
    apply/fsetP=>x;rewrite in_fset0;apply/negP=>hx;apply:hNone;by exists x.
  by move:hCount;rewrite hF cardfs0.
case:(pselect (exists w,w \in F /\z!=w))=>[[w [hw hZW]]|hOnly].
- by exists z,w;split=>//;split.
- have hSubset:F `<=` [fset z].
    apply/fsubsetP=>w hw;rewrite in_fset1;apply/eqP.
    case:(eqVneq w z)=>[h|hDifferent];first exact h.
    exfalso;apply:hOnly;exists w;split=>//;by rewrite eq_sym.
  have hUpper:=fsubset_leq_card hSubset;rewrite cardfs1 in hUpper.
  have hFalse:=leq_trans hCount hUpper;discriminate hFalse.
Qed.
