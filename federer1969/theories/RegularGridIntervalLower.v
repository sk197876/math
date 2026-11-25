(** Federer (1969), 3.3.19, p. 305: a nonempty angular
    interval captures a uniform positive fraction of sufficiently
    fine original child directions. Prove the elementary finite
    lower count from the two complementary intervals. *)
From mathcomp Require Import all_boot all_order all_algebra finmap reals boolp classical_sets lra ring.
From Federer Require Import CyclicGridShiftSeparation CyclicGridIntervalCount.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope fset_scope.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [regular_grid_interval_lower]: among n actual
    directions at angles q k, at least (b-a)/q-1 indices
    lie in [a,b], supporting the late-visit argument in
    3.3.19, p. 305. Empty endpoint intervals are allowed. *)
Theorem regular_grid_interval_lower (R:realType) (q:R) n (F:{fset 'I_n}) (a b:R):
  0<q ->0<=a ->a<=b ->b<=q* n%:R ->
  (forall k:'I_n,a<=q* k%:R ->q* k%:R<=b ->k \in F) ->
  b-a-q<=#|` F|%:R* q.
Proof.
move=>hq ha hab hb hContains.
pose U:{fset 'I_n}:=[fset k | k:'I_n].
pose L:{fset 'I_n}:=[fset k:'I_n | q* k%:R<a].
pose G:{fset 'I_n}:=[fset k:'I_n | b<q* k%:R].
have hLeft k:k \in L ->0<=cyclic_grid_shifted_point q (fun _:'I_n=>false) k /\
    cyclic_grid_shifted_point q (fun _:'I_n=>false) k<=a.
  rewrite /L in_fset /= /cyclic_grid_shifted_point !addr0=>h;split.
  - exact:mulr_ge0 (ltW hq) (ler0n _ _).
  - exact:ltW h.
have hRight k:k \in G ->b<=cyclic_grid_shifted_point q (fun _:'I_n=>false) k /\
    cyclic_grid_shifted_point q (fun _:'I_n=>false) k<=q* n%:R-q.
  rewrite /G in_fset /= /cyclic_grid_shifted_point !addr0=>h;split;first exact:ltW h.
  have hSucc:((k.+1)%:R:R)=k%:R+1 by rewrite -addn1 natrD.
  have hk:(k%:R+1<=n%:R:>R) by rewrite -hSucc ler_nat;exact:ltn_ord.
  nra.
have hL:= @cyclic_grid_interval_count R q n (fun _=>false) L 0 a hq ha hLeft.
have hG:#|` G|%:R*q<=q*n%:R-b.
  case:(leP b (q*n%:R-q))=>hTop.
  - have hPacking:=@cyclic_grid_interval_count R q n (fun _=>false) G b (q*n%:R-q) hq hTop hRight.
    lra.
  - have hEmpty:G=fset0.
      apply/fsetP=>k;rewrite in_fset0;apply/negP=>hk.
      have [hLower hUpper]:=hRight k hk;exfalso;lra.
    rewrite hEmpty cardfs0 mul0r;by lra.
have hUnion:(U `<=` F `|` (L `|` G))%fset.
  apply/fsubsetP=>k _;rewrite !in_fsetU.
  case:(leP a (q* k%:R))=>hA.
  - case:(leP (q* k%:R) b)=>hB.
    + by rewrite (hContains k hA hB).
    + apply/orP;right;apply/orP;right.
      rewrite /G in_fset /=;exact hB.
  - apply/orP;right;apply/orP;left.
    rewrite /L in_fset /=;exact hA.
have hCard:(n<=#|` F|+(#|` L|+#|` G|))%N.
  have hSubset:= fsubset_leq_card hUnion.
  have hU:#|` U|= n.
    rewrite /U card_imfset //=.
    by rewrite -cardE card_ord.
  rewrite hU in hSubset.
  have hOne:(#|` (F `|` (L `|` G))%fset|<=#|` F|+#|` (L `|` G)%fset|)%N.
    rewrite cardfsU;exact:leq_subr.
  have hTwo:(#|` (L `|` G)%fset|<=#|` L|+#|` G|)%N.
    rewrite cardfsU;exact:leq_subr.
  exact:(leq_trans hSubset (leq_trans hOne (leq_add (leqnn _) hTwo))).
have hCardReal:(n%:R<=#|` F|%:R+(#|` L|%:R+#|` G|%:R):>R).
  by rewrite -!natrD ler_nat.
have hWeighted:= ler_wpM2r (ltW hq) hCardReal.
nra.
Qed.
