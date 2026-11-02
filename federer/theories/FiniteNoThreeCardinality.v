(** Federer (1969), 2.10.29, p. 194: supporting finite-family count for the
    assertion that a short interval meets at most two equal-length disjoint
    intervals. A family with no three distinct members has cardinality at
    most two, including the empty family and an empty ambient type. *)
From mathcomp Require Import all_boot all_order finmap boolp.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope fset_scope.
Local Open Scope nat_scope.

(** Source for [finite_family_no_three_cardinality]: supporting
    cardinality form of the at-most-two step
    in 2.10.29, p. 194. This is a
    finite set-theory fact, not a new
    geometric hypothesis or a choice of order. *)
Lemma finite_family_no_three_cardinality (I : choiceType) (F : {fset I}) :
  (forall a b c, a \in F -> b \in F -> c \in F ->
    a!=b -> a!=c -> b!=c -> False) -> #|` F|<=2.
Proof.
move=> hno3.
case: (pselect (exists a, a \in F))=> [[a ha]|hnone]; last first.
  have he : F=fset0 by apply/fsetP=> x; rewrite in_fset0; apply/negP=> hx; apply: hnone; by exists x.
  by rewrite he cardfs0.
case: (pselect (exists b, b \in F /\ b!=a))=> [[b [hb hba]]|hnone].
- have hsub : F `<=` [fset a;b].
    apply/fsubsetP=> c hc; rewrite in_fset2.
    case: (eqVneq c a)=> [hca|hca]; first by [].
    case: (eqVneq c b)=> [hcb|hcb]; first by [].
    exfalso; apply: (@hno3 a b c ha hb hc); by rewrite eq_sym.
  have hh := fsubset_leq_card hsub; rewrite cardfs2 in hh.
  have hab : a!=b by rewrite eq_sym.
  by rewrite hab in hh.
- have hsub : F `<=` [fset a].
    apply/fsubsetP=> b hb; rewrite in_fset1; apply/eqP.
    case: (eqVneq b a)=> [he|hne]; first exact he.
    exfalso; apply: hnone; exists b; by split.
  have hh := fsubset_leq_card hsub; rewrite cardfs1 in hh.
  exact: leq_trans hh (leqnSn 1).
Qed.
