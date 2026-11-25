(** Federer (1969), 3.4.8(10), p. 332:
    select the finite fibre sequences by
    their independent membership and increasing-order
    laws. These are local existence witnesses
    for the original ordered inverse functions. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets cardinality reals.
From Federer Require Import FiniteOrderedEnumeration FiniteFibreEnumerationUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [ordered_fibre_sequences_exist]:
    list each original fibre increasingly by
    omega_(m+1), as in 3.4.8(10),
    p. 332. The finite ordered-sequence
    existence theorem supplies each witness;
    no continuity is assumed in this selection. *)
Theorem ordered_fibre_sequences_exist (R:realType) (X:choiceType) (Y:Type)
    (P:X->Y) (Z:set X) (V:set Y) (xi:X->R):
  (forall y,V y ->finite_set [set x|Z x /\P x = y]) ->
  (forall x z,Z x ->Z z ->P x = P z ->xi x=xi z ->x=z) ->
  exists S:Y->seq X,forall y,V y ->
    is_finite_ordered_enumeration [set x|Z x /\P x = y] xi (S y).
Proof.
move=>hFinite hInjective.
have hEach y:exists s:seq X,V y ->
    is_finite_ordered_enumeration [set x|Z x /\P x = y] xi s.
  case:(pselect (V y))=>[hy|hy].
  - have hInj x z:(Z x /\P x = y) ->(Z z /\P z = y) ->xi x=xi z ->x=z.
      move=>hx hz hEqual;apply:(hInjective x z hx.1 hz.1 _ hEqual).
      by rewrite hx.2 hz.2.
    have [s hs]:=@finite_ordered_enumeration_exists R X [set x|Z x /\P x = y] xi
      (hFinite y hy) hInj.
    by exists s.
  - by exists [::]=>h;exfalso;exact:hy h.
pose S:=fun y:Y=>projT1 (cid (hEach y)).
exists S;move=>y hy;exact:(projT2 (cid (hEach y))) hy.
Qed.

(** Source for [ordered_sequence_fibre_enumeration]:
    index the original ordered fibre by
    0,...,nu-1, 3.4.8(10), p. 332.
    Its exact size, membership and strict
    order supply an injective exhaustive family;
    the chosen default is never used on an index. *)
Theorem ordered_sequence_fibre_enumeration (R:realType) (X:choiceType) (Y:Type)
    (P:X->Y) (Z:set X) (y:Y) (xi:X->R) (x0:X) (s:seq X):
  is_finite_ordered_enumeration [set x|Z x /\P x = y] xi s ->
  is_finite_fibre_enumeration P Z y (fun i:'I_(size s)=>nth x0 s (i:nat)).
Proof.
move=>[hMember hSorted].
have hTrans:transitive (fun x z:X=>xi x<xi z) by move=>x z w;exact:lt_trans.
have hIrr:irreflexive (fun x z:X=>xi x<xi z) by move=>x;exact:ltxx.
have hUniq:uniq s:=@sorted_uniq X (fun x z=>xi x<xi z) hTrans hIrr s hSorted.
split.
- move=>i;exact:(hMember (nth x0 s i)).1 (mem_nth x0 (ltn_ord i)).
split.
- move=>x hx hPx.
  have hIn:x \in s:=(hMember x).2 (conj hx hPx).
  have hIndex:(index x s<size s)%N by rewrite index_mem.
  exists (Ordinal hIndex);exact:nth_index hIn.
- move=>i j hEqual;apply:val_inj;apply/eqP.
  rewrite -(@nth_uniq X x0 s (i:nat) (j:nat) (ltn_ord i) (ltn_ord j) hUniq).
  apply/eqP;exact:hEqual.
Qed.
