(** Federer (1969), corrected 3.4.8(11), p. 327:
    append a regular stratum after the smaller-dimensional
    strata. The exact finite union and earlier-index
    equations preserve the published ordering of boundaries. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets.
From Federer Require Import InfiniteSequence.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [ordinal_set_family_snoc_union]:
    adding the last stratum adds exactly its
    set to the union, supporting corrected
    3.4.8(11), p. 327. *)
Lemma ordinal_set_family_snoc_union (X:Type) mu (S:'I_mu->set X) (A:set X):
  (\bigcup_(i:'I_mu.+1) ordinal_snoc S A i) = (\bigcup_i S i) `|` A.
Proof.
apply/seteqP;split=>x.
- move=>[i _ hx];case:(unliftP ord_max i)=>[j ->|->] in hx.
  + left;exists j;first exact:Logic.I.
    by rewrite ordinal_snoc_lift in hx.
  + right;by rewrite ordinal_snoc_last in hx.
- move=>[[i _ hx]|hx].
  + exists (lift ord_max i);first exact:Logic.I.
    by rewrite ordinal_snoc_lift.
  + exists ord_max;first exact:Logic.I.
    by rewrite ordinal_snoc_last.
Qed.

(** Source for [ordinal_set_family_snoc_earlier]:
    the earlier strata of each old index
    stay unchanged after appending the new stratum,
    corrected 3.4.8(11), p. 327. *)
Lemma ordinal_set_family_snoc_earlier (X:Type) mu (S:'I_mu->set X) (A:set X) (i:'I_mu):
  (\bigcup_(j in [set j:'I_mu.+1|(j<lift ord_max i)%N]) ordinal_snoc S A j) =
    \bigcup_(j in [set j:'I_mu|(j<i)%N]) S j.
Proof.
apply/seteqP;split=>x.
- move=>[j hJI hx];case:(unliftP ord_max j)=>[k ->|->] in hJI hx.
  + have hOriginal:(lift ord_max k<lift ord_max i)%N:=hJI.
    have hLess:(k<i)%N by rewrite !lift_max in hOriginal.
    exists k;first exact:hLess.
    by rewrite ordinal_snoc_lift in hx.
  + have hOriginal:((ord_max:'I_mu.+1)<lift ord_max i)%N:=hJI.
    have hLess:(mu<i)%N by rewrite lift_max in hOriginal.
    have hFalse:=ltn_trans hLess (ltn_ord i);by rewrite ltnn in hFalse.
- move=>[j hJI hx].
  have hRaised:(lift ord_max j<lift ord_max i)%N by rewrite !lift_max;exact:hJI.
  exists (lift ord_max j);first exact:hRaised.
  by rewrite ordinal_snoc_lift.
Qed.

(** Source for [ordinal_set_family_snoc_before_last]:
    the earlier strata of the appended index
    are exactly the old union, as required
    by corrected 3.4.8(11), p. 327. *)
Lemma ordinal_set_family_snoc_before_last (X:Type) mu (S:'I_mu->set X) (A:set X):
  (\bigcup_(j in [set j:'I_mu.+1|(j<(ord_max:'I_mu.+1))%N]) ordinal_snoc S A j) = \bigcup_i S i.
Proof.
apply/seteqP;split=>x.
- move=>[j hJ hx];case:(unliftP ord_max j)=>[k ->|->] in hJ hx.
  + exists k;first exact:Logic.I.
    by rewrite ordinal_snoc_lift in hx.
  + have hFalse:((ord_max:'I_mu.+1)<ord_max)%N:=hJ.
    by rewrite ltnn in hFalse.
- move=>[j _ hx].
  have hRaised:(lift ord_max j<(ord_max:'I_mu.+1))%N by rewrite lift_max;exact:ltn_ord j.
  exists (lift ord_max j);first exact:hRaised.
  by rewrite ordinal_snoc_lift.
Qed.
