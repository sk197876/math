(** Federer (1969), 3.4.5, p. 321: supporting
    finite order argument for maximal irreducible components.
    A finite nonempty preordered family has a maximal member,
    and every member lies below a maximal one. *)
From mathcomp Require Import all_boot boolp.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Section Maximum.
Variable Y:choiceType.
Variable pre:Y->Y->Prop.
Hypothesis hRefl:forall x,pre x x.
Hypothesis hTrans:forall x y z,pre x y ->pre y z ->pre x z.

(** Source for [finite_preorder_maximal_member]: a finite
    family has a maximal member, supporting the maximality
    clause of 3.4.5, p. 321. *)
Lemma finite_preorder_maximal_member (F:seq Y):F!=[::] ->
  exists m,m \in F /\forall y,y \in F ->pre m y ->pre y m.
Proof.
elim:F=>[|x F ih] hNonempty;first by rewrite eqxx in hNonempty.
clear hNonempty;case:F ih=>[|z F] ih.
- exists x;split;first exact:mem_head.
  move=>y;rewrite in_cons in_nil orbF=>/eqP ->;by move=>_.
- have [m [hM hMaximum]]:=ih isT.
  case:(pselect (pre m x))=>[hMX|hNotMX].
  + exists x;split;first exact:mem_head.
    move=>y;rewrite in_cons;move/orP=>[/eqP ->|hY] hXY;first exact:hRefl.
    have hMY:=@hTrans m x y hMX hXY.
    have hYM:=hMaximum y hY hMY.
    exact:(@hTrans y m x hYM hMX).
  + exists m;split;first by rewrite in_cons hM orbT.
    move=>y;rewrite in_cons;move/orP=>[/eqP ->|hY] hMY.
    * exfalso;exact:hNotMX hMY.
    * exact:hMaximum y hY hMY.
Qed.

(** Source for [finite_preorder_maximum_above_member]: each
    member of a finite family is contained in a maximal
    member, supporting irreducible components in 3.4.5, p. 321. *)
Theorem finite_preorder_maximum_above_member (F:seq Y) (x:Y):x \in F ->
  exists m,m \in F /\pre x m /\forall y,y \in F ->pre m y ->pre y m.
Proof.
move=>hX.
pose B:seq Y:=[seq y<-F|`[<pre x y>]].
have hXB:x \in B by rewrite /B mem_filter;apply/andP;split;[apply/asboolP;exact:hRefl|exact:hX].
have hNonempty:B!=[::].
  apply/eqP=>hEmpty;by rewrite hEmpty in_nil in hXB.
have [m [hM hMaximum]]:=finite_preorder_maximal_member hNonempty.
move:hM;rewrite /B mem_filter=>/andP [/asboolP hXM hMF].
exists m;split;first exact:hMF.
split;first exact:hXM.
move=>y hY hMY;apply:hMaximum;last exact:hMY.
rewrite /B mem_filter;apply/andP;split;last exact:hY.
apply/asboolP;exact:(@hTrans x m y hXM hMY).
Qed.
End Maximum.
