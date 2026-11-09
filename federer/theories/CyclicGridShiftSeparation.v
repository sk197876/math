(** Federer (1969), 3.3.19, p. 302: elementary
    separation of lifted cyclic scalar grid points. Lifting
    across the angular cut preserves the original minimum
    grid spacing, including the wrap-around pair. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets lra ring.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Section Grid.
Variable R:realType.

(** Source for [cyclic_grid_shifted_point]: a local lift
    of an original cyclic angle by either zero or its
    full period, supporting the halfplane count in
    3.3.19, p. 302. The branch is auxiliary. *)
Definition cyclic_grid_shifted_point (q:R) n (b:'I_n->bool) (k:'I_n):R:=
  q*(k%:R+(if b k then n%:R else 0)).

(** Source for [cyclic_grid_shift_separation]: every
    two distinct original indices remain separated by
    at least one actual grid step after any such
    local period lifts, supporting 3.3.19, p. 302. *)
Lemma cyclic_grid_shift_separation (q:R) n (b:'I_n->bool) (k l:'I_n):
  0<q ->k!= l ->q<=`|cyclic_grid_shifted_point q b k-cyclic_grid_shifted_point q b l|.
Proof.
move=>hq hKL.
have hSucc (i:nat):(i.+1%:R:R)= i%:R+1 by rewrite -addn1 natrD.
have hk0:(0<= k%:R:>R) by rewrite ler0n.
have hl0:(0<= l%:R:>R) by rewrite ler0n.
have hkN:(k%:R+1<= n%:R:>R) by rewrite -hSucc ler_nat;exact:ltn_ord.
have hlN:(l%:R+1<= n%:R:>R) by rewrite -hSucc ler_nat;exact:ltn_ord.
have hOrdered i j:(i<j)%N ->(1<= j%:R-i%:R:>R).
  move=>hij;have hh:(i.+1%:R<= j%:R:>R) by rewrite ler_nat.
  rewrite hSucc in hh;lra.
have hCases:(k<l)%N \/(l<k)%N.
  case:(ltngtP k l)=>[h|h|h];[by left|by right|].
  have hEqual:k= l by apply:val_inj.
  by move:hKL;rewrite hEqual eqxx.
rewrite /cyclic_grid_shifted_point.
case:(b k);case:(b l)=>/=;rewrite ler_normr;apply/orP.
- case:hCases=>[hkl|hlk].
  + right;have hGap:= hOrdered k l hkl;nra.
  + left;have hGap:= hOrdered l k hlk;nra.
- left;nra.
- right;nra.
- case:hCases=>[hkl|hlk].
  + right;have hGap:= hOrdered k l hkl;nra.
  + left;have hGap:= hOrdered l k hlk;nra.
Qed.

(** Source for [cyclic_grid_shift_injective]: a lifted
    representation does not duplicate any original index,
    supporting exact finite arc counts in 3.3.19, p. 302. *)
Lemma cyclic_grid_shift_injective (q:R) n (b:'I_n->bool):
  0<q ->injective (cyclic_grid_shifted_point q b).
Proof.
move=>hq k l hEqual;case:(eqVneq k l)=>[h|hKL];first exact h.
have hGap:=@cyclic_grid_shift_separation q n b k l hq hKL.
rewrite hEqual subrr normr0 in hGap.
have hFalse:= lt_le_trans hq hGap;by rewrite ltxx in hFalse.
Qed.
End Grid.
