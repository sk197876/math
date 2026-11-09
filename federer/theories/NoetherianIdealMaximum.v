(** Federer (1969), 3.4.5, p. 321: the
    Noetherian hypothesis implies the maximal-ideal-family property
    needed for minimal analytic variety germs. An ascending
    chain union has finitely many generators and must stabilise. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets.
From Federer Require Import CommutativeIdealUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [noetherian_ideal_family_maximum]: the algebraic
    step behind the nonempty-family minimal-member assertion
    of 3.4.5, p. 321. Every nonempty family
    of actual ideals in a Noetherian ring has an
    inclusion-maximal member. No chain or geometric conclusion
    is supplied as an extra hypothesis. *)
Theorem noetherian_ideal_family_maximum (A:comNzRingType) (F:set (set A)):
  is_noetherian_commutative_ring A ->(exists I,F I) ->
  (forall I,F I ->is_commutative_ideal I) ->
  exists I,F I /\forall J,F J ->I `<=` J ->J `<=` I.
Proof.
move=>hNoetherian [I0 hI0] hIdeals;apply:contrapT=>hNoMaximum.
have hStep I:F I ->exists J,F J /\I `<=` J /\~J `<=` I.
  move=>hI;case:(pselect (exists J,F J /\I `<=` J /\~J `<=` I))=>[h|h];first exact:h.
  exfalso;apply:hNoMaximum;exists I;split;first exact:hI.
  move=>J hJ hIJ;apply:contrapT=>hJI;apply:h;exists J;by split;last split.
pose next I:=if pselect (F I) is left h then projT1 (cid (hStep I h)) else I0.
have hNext I (hI:F I):F (next I) /\I `<=` next I /\~next I `<=` I.
  rewrite /next;case:pselect=>[h|h];last by exfalso;exact:h hI.
  exact:(projT2 (cid (hStep I h))).
pose u n:=iter n next I0.
have hUS n:u n.+1=next (u n) by rewrite /u iterS.
have hUF n:F (u n).
  elim:n=>[|n ih];first exact:hI0.
  rewrite hUS;exact:(hNext _ ih).1.
have hAscending n:u n `<=` u n.+1 by rewrite hUS;exact:(hNext _ (hUF n)).2.1.
have hStrict n:~u n.+1 `<=` u n by rewrite hUS;exact:(hNext _ (hUF n)).2.2.
have hMono i j:(i<=j)%N ->u i `<=` u j.
  elim:j=>[|j ih] hIJ.
  - have /eqP hi:i==0%N by rewrite -leqn0.
    subst i;by move=>x hx.
  - move:hIJ;rewrite leq_eqVlt;move/orP=>[/eqP ->|hIJ];first by move=>x hx.
    move=>x hx;exact:(hAscending j x (ih hIJ x hx)).
pose U:set A:=fun x=>exists n,u n x.
have hU:is_commutative_ideal U.
  constructor.
  - exists 0%N;exact:commutative_ideal_zero (hIdeals _ (hUF 0%N)).
  - move=>x y [i hi] [j hj];exists (maxn i j).
    exact:(@commutative_ideal_add A _ (hIdeals _ (hUF (maxn i j))) x y
      (hMono i _ (leq_maxl i j) x hi) (hMono j _ (leq_maxr i j) y hj)).
  - move=>x [i hi];exists i;exact:(@commutative_ideal_opp A _ (hIdeals _ (hUF i)) x hi).
  - move=>x y [i hi];exists i;exact:(@commutative_ideal_mul A _ (hIdeals _ (hUF i)) x y hi).
have [G hGenerated]:=hNoetherian U hU.
have hFiniteBound:forall B:seq A,(forall x,x \in B ->U x) ->
    exists n,forall x,x \in B ->u n x.
  elim=>[|x B ih] hB.
  - exists 0%N=>y;by rewrite in_nil.
  - have [i hi]:=hB x (mem_head x B).
    have hBT y (hy:y \in B):U y.
      apply:hB;by rewrite in_cons hy orbT.
    have [j hj]:=ih hBT.
    exists (maxn i j)=>y;rewrite in_cons;move/orP=>[/eqP ->|hy].
    + exact:(hMono i _ (leq_maxl i j) x hi).
    + exact:(hMono j _ (leq_maxr i j) y (hj y hy)).
have [N hN]:=hFiniteBound G (generated_commutative_ideal_contains hGenerated).
have hContained:U `<=` u N.
  exact:(generated_commutative_ideal_minimal hGenerated (hIdeals _ (hUF N)) hN).
apply:(hStrict N)=>x hx;apply:hContained;by exists N.+1.
Qed.
