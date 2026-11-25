(** Federer (1969), 4.1.6, p. 352: the actual
    tuple in v^(i) is the ordered tuple obtained
    by deleting its i-th entry. This supporting
    identity connects the book formula to the earlier
    word contraction, without changing the order. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions.
From Federer Require Import ExteriorDifferentialUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [exterior_omitted_tuple_values]: the
    original ordered omission in Federer 4.1.6,
    p. 352, expressed by its exact underlying list. *)
Lemma exterior_omitted_tuple_values (K:fieldType) (V:lmodType K) m
    (t:m.+1.-tuple V) (i:'I_m.+1):
  val (exterior_omitted_tuple t i)=take i t++drop i.+1 t.
Proof.
have hi:(i<=m)%N by move:(ltn_ord i); rewrite ltnS.
have hSize:size (take i t++drop i.+1 t)=m.
  rewrite size_cat size_take_min size_drop !size_tuple (minn_idPl (ltnW (ltn_ord i))) subSS.
  by rewrite addnC (subnK hi).
apply (@eq_from_nth V (0:V) (val (exterior_omitted_tuple t i)) (take i t++drop i.+1 t)).
- by rewrite size_tuple hSize.
move=>k hk; rewrite size_tuple in hk.
pose j:'I_m:=Ordinal hk.
change (nth 0 (exterior_omitted_tuple t i) j=nth 0 (take i t++drop i.+1 t) j).
rewrite -(tnth_nth 0) /exterior_omitted_tuple tnth_mktuple (tnth_nth 0).
change (nth 0 t (bump i j)=nth 0 (take i t++drop i.+1 t) j).
rewrite nth_cat size_take_min size_tuple (minn_idPl (ltnW (ltn_ord i))).
case hji:(j<i)%N.
- rewrite /bump leqNgt hji /= add0n.
  by rewrite nth_take.
- have hij:(i<=j)%N by rewrite leqNgt hji.
  rewrite /bump hij /= add1n nth_drop.
  congr (nth 0 t _); by rewrite addSn (subnKC hij).
Qed.
