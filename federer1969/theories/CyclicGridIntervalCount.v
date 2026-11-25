(** Federer (1969), 3.3.19, p. 305: elementary finite
    angular count underlying the printed a+2/n estimate. *)
From mathcomp Require Import all_boot all_order all_algebra finmap reals boolp classical_sets lra ring.
From Federer Require Import CyclicGridShiftSeparation FiniteSeparatedRealInterval.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope fset_scope.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [cyclic_grid_interval_count]: the number of
    actual lifted cyclic angles in a closed interval of length
    L is at most L/q+1, supporting the proper-arc count
    in 3.3.19, p. 305. Original index labels are
    retained, so no point is counted twice across the cut. *)
Theorem cyclic_grid_interval_count (R:realType) (q:R) n (b:'I_n->bool)
    (F:{fset 'I_n}) (a c:R):
  0<q ->a<=c ->
  (forall k,k \in F ->a<=cyclic_grid_shifted_point q b k /\
    cyclic_grid_shifted_point q b k<=c) ->
  #|` F|%:R*q<=c-a+q.
Proof.
move=>hq hac hInside.
pose G:{fset R}:=[fset cyclic_grid_shifted_point q b k | k in F].
have hGInside x:x \in G ->a<=x /\x<=c.
  move=>/imfsetP[k hk ->];exact:hInside k hk.
have hGSeparated x y:x \in G ->y \in G ->x!=y ->q<=`|x-y|.
  move=>/imfsetP[k hk ->] /imfsetP[l hl ->] hKL.
  have hIndices:k!=l.
    apply/negP=>/eqP hEqual;by move:hKL;rewrite hEqual eqxx.
  exact:(@cyclic_grid_shift_separation R q n b k l hq hIndices).
have hCard:#|` G|= #|` F|.
  rewrite /G card_imfset;last exact:(@cyclic_grid_shift_injective R q n b hq).
  exact:erefl.
have hPacking:=@finite_separated_real_interval_bound R G a c q hq hac hGInside hGSeparated.
by rewrite hCard in hPacking.
Qed.
