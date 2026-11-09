(** Federer (1969), 3.3.20, p. 307:
    overlapping original projected closed intervals merge exactly. *)
From mathcomp Require Import all_boot all_order all_algebra reals classical_sets lra.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [closed_segment_overlap_union]: supporting
    merging of original projected intervals in 3.3.20,
    p. 307, including touching endpoints in
    the correction of published erratum p. 6,
    book p. 307 line 26. *)
Lemma closed_segment_overlap_union (R:realType) (a b c d:R):
  a<=c ->c<=b ->b<=d ->
  ((`[a,b] `|` `[c,d]):set R)=`[a,d].
Proof.
move=>hac hcb hbd;apply/seteqP;split=>x.
- move=>[hx|hx];move:hx;rewrite /= !in_itv /= =>/andP[h0 h1];apply/andP;split;lra.
- rewrite /= in_itv /= =>/andP[h0 h1].
  case:(leP x b)=>hXB.
  + left;rewrite /= in_itv /=;by apply/andP;split.
  + right;rewrite /= in_itv /=;apply/andP;split=>//;lra.
Qed.
