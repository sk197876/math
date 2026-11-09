(** Federer (1969), 3.3.19, p. 302: elementary
    finite union counting before the geometric disjointness
    argument. Duplicate image indices can only reduce the count. *)
From mathcomp Require Import all_boot all_order all_algebra finmap.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope fset_scope.
Local Open Scope nat_scope.

(** Source for [finite_fset_union_card_upper]: supporting
    the successive original disc counts of 3.3.19,
    p. 302. No pairwise disjointness is assumed here. *)
Lemma finite_fset_union_card_upper (I X:choiceType) (H:{fset I}) (F:I->{fset X}):
  (#|` (\bigcup_(i<-H) F i)%fset|<=\sum_(i<-H) #|` F i|)%N.
Proof.
elim/fset1U_rect:H=>[|i H hi ih];first by rewrite !big_nil cardfs0.
rewrite !big_fsetU1 //.
apply:(leq_trans (_ : #|` (F i `|` (\bigcup_(j<-H) F j))%fset|<=
  #|` F i|+#|` (\bigcup_(j<-H) F j)%fset|)).
- rewrite cardfsU;exact:leq_subr.
- exact:leq_add (leqnn _) ih.
Qed.
