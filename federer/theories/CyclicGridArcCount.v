(** Federer (1969), 3.3.19, p. 302: exact
    finite count for a proper angular interval containing
    lifted original cyclic indices. Strict endpoints retain
    the integer improvement for odd subdivisions. *)
From mathcomp Require Import all_boot all_order all_algebra finmap reals boolp classical_sets lra ring.
From Federer Require Import CyclicGridShiftSeparation FiniteSeparatedOpenInterval.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope fset_scope.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section Count.
Variable R:realType.

(** Source for [cyclic_grid_arc_count]: an original
    regular n-grid has at most n/2+1 indices in
    an open interval of length at most (n+1)/2
    grid steps, supporting 3.3.19, p. 302.
    The statement is expressed without rounding or real
    coercion ambiguity as 2 card(F)<=n+2. *)
Theorem cyclic_grid_arc_count (q:R) n (b:'I_n->bool)
    (F:{fset 'I_n}) (a c:R):
  0<q ->a<c ->c-a<=((n%:R+1)/2)* q ->
  (forall k,k \in F ->a<cyclic_grid_shifted_point q b k /\
    cyclic_grid_shifted_point q b k<c) ->
  (2*#|` F|<=n+2)%N.
Proof.
move=>hq hac hSpan hInside.
pose G:{fset R}:=[fset cyclic_grid_shifted_point q b k | k in F].
have hGInside x:x \in G ->a<x /\x<c.
  move=>/imfsetP[k hk ->];exact:hInside k hk.
have hGSeparated x y:x \in G ->y \in G ->x!=y ->q<=`|x-y|.
  move=>/imfsetP[k hk ->] /imfsetP[l hl ->] hKL.
  have hIndices:k!=l.
    apply/negP=>/eqP hEqual;by move:hKL;rewrite hEqual eqxx.
  exact:(@cyclic_grid_shift_separation R q n b k l hq hIndices).
have hCard:#|` G|=#|` F|.
  rewrite /G card_imfset;last exact:(@cyclic_grid_shift_injective R q n b hq).
  exact:erefl.
have hPacking:=@finite_separated_open_interval_bound R G a c q hq hac hGInside hGSeparated.
rewrite hCard in hPacking.
have hReal:(2*#|` F|%:R<n%:R+3:>R) by nra.
have hNat:(2*#|` F|<n+3)%N.
  have hCast:(((2*#|` F|)%N)%:R<((n+3)%N)%:R:>R) by rewrite natrM natrD;exact:hReal.
  by move:hCast;rewrite ltr_nat.
have hSucc:(n+3=(n+2).+1)%N by rewrite addnS.
by move:hNat;rewrite hSucc ltnS.
Qed.
End Count.
