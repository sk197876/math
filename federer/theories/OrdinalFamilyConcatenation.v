(** Federer (1969), 3.4.8(11), p. 333:
    concatenate the finite stratum families from
    successive irreducible components. The index order
    retains all first-family strata before the second
    family, exactly as in the printed successive differences. *)
From mathcomp Require Import all_boot all_order boolp classical_sets.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [ordinal_family_cat]:
    the prescribed concatenation of the original finite
    index lists in 3.4.8(11), p. 333. *)
Definition ordinal_family_cat (X:Type) p q (F:'I_p->X) (G:'I_q->X) (i:'I_(p+q)):X:=
  match split i with inl j=>F j|inr j=>G j end.

(** Source for [ordinal_family_cat_left]:
    the first family retains its original values,
    supporting 3.4.8(11), p. 333. *)
Lemma ordinal_family_cat_left (X:Type) p q (F:'I_p->X) (G:'I_q->X) (i:'I_p):
  ordinal_family_cat F G (lshift q i) = F i.
Proof.
change (match split (unsplit (inl i:'I_p+'I_q)) with inl j=>F j|inr j=>G j end = F i).
by rewrite unsplitK.
Qed.

(** Source for [ordinal_family_cat_right]:
    the second family retains its original values,
    supporting 3.4.8(11), p. 333. *)
Lemma ordinal_family_cat_right (X:Type) p q (F:'I_p->X) (G:'I_q->X) (i:'I_q):
  ordinal_family_cat F G (rshift p i) = G i.
Proof.
change (match split (unsplit (inr i:'I_p+'I_q)) with inl j=>F j|inr j=>G j end = G i).
by rewrite unsplitK.
Qed.

(** Source for [ordinal_set_family_cat_union]:
    concatenation gives precisely the union of the
    original two stratum unions, 3.4.8(11), p. 333. *)
Lemma ordinal_set_family_cat_union (X:Type) p q (F:'I_p->set X) (G:'I_q->set X):
  (\bigcup_(i:'I_(p+q)) ordinal_family_cat F G i) = (\bigcup_i F i) `|` (\bigcup_j G j).
Proof.
apply/seteqP;split.
- move=>x [i _ hx];case:(split_ordP i)=>[j ->|j ->] in hx.
  + left;exists j;first exact:Logic.I.
    by rewrite ordinal_family_cat_left in hx.
  + right;exists j;first exact:Logic.I.
    by rewrite ordinal_family_cat_right in hx.
- move=>x [[i _ hx]|[j _ hx]].
  + exists (lshift q i);first exact:Logic.I.
    by rewrite ordinal_family_cat_left.
  + exists (rshift p j);first exact:Logic.I.
    by rewrite ordinal_family_cat_right.
Qed.

(** Source for [ordinal_set_family_cat_earlier_left]:
    earlier indices of a first-family stratum remain
    its original earlier indices, 3.4.8(11), p. 333. *)
Lemma ordinal_set_family_cat_earlier_left (X:Type) p q (F:'I_p->set X) (G:'I_q->set X) (i:'I_p):
  (\bigcup_(j in [set j:'I_(p+q)|(j<lshift q i)%N]) ordinal_family_cat F G j) =
    \bigcup_(j in [set j:'I_p|(j<i)%N]) F j.
Proof.
apply/seteqP;split.
- move=>x [j hEarlier hx];case:(split_ordP j)=>[k ->|k ->] in hEarlier hx.
  + have hLess:(k<i)%N:=hEarlier.
    exists k;first exact:hLess.
    by rewrite ordinal_family_cat_left in hx.
  + have hBad:(p+k<i)%N:=hEarlier.
    have hP:(p<=p+k)%N:=leq_addr _ _.
    have hImpossible:=leq_ltn_trans hP (ltn_trans hBad (ltn_ord i)).
    by rewrite ltnn in hImpossible.
- move=>x [j hEarlier hx].
  exists (lshift q j);first exact:hEarlier.
  by rewrite ordinal_family_cat_left.
Qed.

(** Source for [ordinal_set_family_cat_earlier_right]:
    earlier indices of a second-family stratum consist
    of the entire first family and its own
    earlier second-family indices, 3.4.8(11), p. 333. *)
Lemma ordinal_set_family_cat_earlier_right (X:Type) p q (F:'I_p->set X) (G:'I_q->set X) (i:'I_q):
  (\bigcup_(j in [set j:'I_(p+q)|(j<rshift p i)%N]) ordinal_family_cat F G j) =
    (\bigcup_j F j) `|` (\bigcup_(j in [set j:'I_q|(j<i)%N]) G j).
Proof.
apply/seteqP;split.
- move=>x [j hEarlier hx];case:(split_ordP j)=>[k ->|k ->] in hEarlier hx.
  + left;exists k;first exact:Logic.I.
    by rewrite ordinal_family_cat_left in hx.
  + have hLess:(k<i)%N.
      have hRaised:(p+k<p+i)%N:=hEarlier;by rewrite ltn_add2l in hRaised.
    right;exists k;first exact:hLess.
    by rewrite ordinal_family_cat_right in hx.
- move=>x [[j _ hx]|[j hEarlier hx]].
  + have hLess:(j<p+i)%N:=leq_trans (ltn_ord j) (leq_addr _ _).
    exists (lshift q j);first exact:hLess.
    by rewrite ordinal_family_cat_left.
  + have hLess:(p+j<p+i)%N by rewrite ltn_add2l.
    exists (rshift p j);first exact:hLess.
    by rewrite ordinal_family_cat_right.
Qed.
