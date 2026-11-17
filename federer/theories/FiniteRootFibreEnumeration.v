(** Federer (1969), 3.4.12, p. 339: transfer the exact
    finite root enumeration to the original projection fibre.
    This connection uses membership, realisation and the proved
    injectivity of the transverse coordinate, without an ordering. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets.
From Federer Require Import FiniteFibreEnumerationUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
(** Source for [finite_root_fibre_enumeration]: an exact list
    of k roots gives an injective exhaustive family indexed by
    0 through k minus one in the original fibre, supporting
    3.4.12, p. 339. The list and chosen points remain local
    existence witnesses; no global complex sheet order is imposed. *)
Theorem finite_root_fibre_enumeration (K:fieldType) (X:choiceType) (Y:Type)
    (P:X->Y) (Z:set X) (y:Y) (xi:X->K) k (roots:seq K):
  uniq roots ->size roots=k ->
  (forall x,Z x ->P x=y ->xi x \in roots) ->
  (forall z,z \in roots ->exists x,Z x /\P x=y /\xi x=z) ->
  (forall x z,Z x ->Z z ->P x=y ->P z=y ->xi x=xi z ->x=z) ->
  exists a:'I_k->X,is_finite_fibre_enumeration P Z y a.
Proof.
move=>hUnique hCount hMember hLift hInjective.
have hBound (i:'I_k):(i<size roots)%N by rewrite hCount;exact:ltn_ord.
have hEach (i:'I_k):exists x,Z x /\P x=y /\xi x=nth 0 roots i.
  exact:hLift _ (mem_nth 0 (hBound i)).
have [a hA]:=choice hEach.
exists a;split.
- move=>i;split;[exact:(hA i).1|exact:(hA i).2.1].
split.
- move=>x hx hPx.
  have hIn:=hMember x hx hPx.
  have hIndex:(index (xi x) roots<k)%N by rewrite -hCount index_mem.
  pose i:'I_k:=Ordinal hIndex.
  exists i;apply:(hInjective _ _ (hA i).1 hx (hA i).2.1 hPx).
  by rewrite (hA i).2.2 /i /= nth_index.
- move=>i j hEqual;apply:val_inj;apply/eqP.
  rewrite -(@nth_uniq K 0 roots (i:nat) (j:nat) (hBound i) (hBound j) hUnique).
  apply/eqP;rewrite -(hA i).2.2 -(hA j).2.2;by rewrite hEqual.
Qed.
