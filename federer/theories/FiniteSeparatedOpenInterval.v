(** Federer (1969), 3.3.19, p. 302: strict
    interval packing for the original angular grid.
    Strict endpoints give the exact integer halfplane bound,
    including odd original subdivision numbers. *)
From mathcomp Require Import all_boot all_order all_algebra finmap reals boolp classical_sets cardinality lra.
From Federer Require Import FiniteRealMaximum FiniteSeparatedRealInterval.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope fset_scope.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [finite_separated_open_interval_bound]:
    if every original point lies strictly between a and b,
    then card(F)q<b-a+q, supporting the strict angular
    count of 3.3.19, p. 302. The empty family
    and arbitrary positive real grid steps are retained. *)
Theorem finite_separated_open_interval_bound (R:realType) (F:{fset R}) (a b q:R):
  0<q ->a<b ->
  (forall x,x \in F ->a<x /\x<b) ->
  (forall x y,x \in F ->y \in F ->x!=y ->q<=`|x-y|) ->
  #|` F|%:R*q<b-a+q.
Proof.
move=>hq hab hBounds hSeparated.
case:(pselect ([set` F]!=set0))=>[hNonempty|hEmpty].
- have hFinite:finite_set [set` F] by apply/finite_fsetP;by exists F.
  have [x [hx hMinimum]]:=@finite_nonempty_real_maximum R R [set` F]
    (fun x:R=> -x) hFinite hNonempty.
  have hMin y:y \in F ->x<=y.
    move=>hy;have hh:=hMinimum y hy;by rewrite lerN2 in hh.
  have [hax hxb]:=hBounds x hx.
  pose l:R:=(a+x)/2.
  have hal:a<l by rewrite /l;lra.
  have hlx:l<=x by rewrite /l;lra.
  have hlb:l<=b by rewrite /l;lra.
  have hClosed y:y \in F ->l<=y /\y<=b.
    move=>hy;have hh:=hMin y hy;have hb:=(hBounds y hy).2;split;lra.
  have hPacking:=@finite_separated_real_interval_bound R F l b q hq hlb hClosed hSeparated.
  lra.
- have hF:F=fset0.
    apply/fsetP=>x;rewrite in_fset0;apply/negP=>hx;apply:hEmpty;by exists x.
  rewrite hF cardfs0 mul0r;lra.
Qed.
