(** Federer (1969), 3.3.19, p. 302: elementary
    finite interval packing behind the original circular
    halfplane count. The proof uses only finite sets and
    scalar order, retaining both closed endpoints. *)
From mathcomp Require Import all_boot all_order all_algebra finmap reals boolp classical_sets cardinality lra.
From Federer Require Import FiniteRealMaximum.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope fset_scope.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [finite_separated_real_interval_bound]:
    a finite set of q-separated original scalar points
    in [a,b] has card(F)q<=b-a+q, supporting the
    cyclic count in 3.3.19, p. 302. Its minimum
    is proved to exist locally; no ordering is supplied. *)
Theorem finite_separated_real_interval_bound (R:realType) (F:{fset R}) (a b q:R):
  0<q ->a<=b ->
  (forall x,x \in F ->a<=x /\x<=b) ->
  (forall x y,x \in F ->y \in F ->x!=y ->q<=`|x-y|) ->
  #|` F|%:R*q<=b-a+q.
Proof.
have hInd:forall N:nat,forall G:{fset R},#|` G|=N ->forall l u d:R,
    0<d ->l<=u ->
    (forall x,x \in G ->l<=x /\x<=u) ->
    (forall x y,x \in G ->y \in G ->x!=y ->d<=`|x-y|) ->
    #|` G|%:R*d<=u-l+d.
  move=>N;elim/ltn_ind:N=>N ih G hCard l u d hd hlu hBounds hSeparated.
  case:(pselect ([set` G]!=set0))=>[hNonempty|hEmpty];last first.
    have hG:G=fset0.
      apply/fsetP=>x;rewrite in_fset0;apply/negP=>hx;apply:hEmpty;by exists x.
    rewrite hG cardfs0 mul0r;lra.
  have hFinite:finite_set [set` G] by apply/finite_fsetP;by exists G.
  have [x [hx hMin]]:=@finite_nonempty_real_maximum R R [set` G] (fun x:R=> -x)
    hFinite hNonempty.
  have hMin' y:y \in G ->x<=y.
    move=>hy;have hh:=hMin y hy;by rewrite lerN2 in hh.
  pose K:{fset R}:=(G `\ x)%fset.
  have hCount:#|` G|=(#|` K|).+1.
    by rewrite (cardfsD1 x) hx add1n.
  have hSmaller:(#|` K|<N)%N by rewrite -hCard hCount.
  have hInside y:y \in K ->x+d<=y /\y<=u.
    move=>hy;have /andP[hyx hyG]:(y!=x) &&(y \in G) by move:hy;rewrite /K !inE.
    have hxy:=hMin' y hyG.
    have hGap:=hSeparated y x hyG hx hyx.
    rewrite ger0_norm ?subr_ge0 // in hGap.
    split;first by lra.
    exact:(hBounds y hyG).2.
  case:(pselect ([set` K]!=set0))=>[hKNonempty|hKEmpty].
  - have [y hy]:=hKNonempty.
    have hNewBounds:x+d<=u by have hh:=hInside y hy;lra.
    have hNewSeparation v w:v \in K ->w \in K ->v!=w ->d<=`|v-w|.
      move=>hv hw hvw;apply:hSeparated=>//.
      + by move:hv;rewrite /K !inE=>/andP[_ hv].
      + by move:hw;rewrite /K !inE=>/andP[_ hw].
    have hRest:=ih #|` K| hSmaller K erefl (x+d) u d hd hNewBounds hInside hNewSeparation.
    have hxBounds:=hBounds x hx.
    rewrite hCount -addn1 natrD;lra.
  - have hK:K=fset0.
      apply/fsetP=>y;rewrite in_fset0;apply/negP=>hy;apply:hKEmpty;by exists y.
    rewrite hCount hK cardfs0 mul1r;lra.
exact:(hInd #|` F| F erefl a b q).
Qed.
