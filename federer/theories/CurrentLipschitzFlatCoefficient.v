(** Federer (1969), 4.1.14, p. 371: the exact
    maximum of the two adjacent exterior-power bounds
    is the compact flat operator coefficient. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [current_lipschitz_flat_coefficient]: the exact
    coefficient sup{Lip(f|K)^m,Lip(f|K)^(m+1)} in Federer
    4.1.14, p. 371. In degree zero it is max(1,L). *)
Definition current_lipschitz_flat_coefficient (R:realType) (m:nat) (L:R):R:=
  Num.max (L^+m) (L^+m.+1).

(** Source for [current_lipschitz_flat_coefficient_nonnegative]:
    positivity of the printed coefficient, supporting Federer
    4.1.14, p. 371. This retains the case L=0 and m=0. *)
Lemma current_lipschitz_flat_coefficient_nonnegative (R:realType) m (L:R):
  0<=L ->0<=current_lipschitz_flat_coefficient m L.
Proof.
move=>hL;rewrite /current_lipschitz_flat_coefficient le_max.
by rewrite (exprn_ge0 m hL).
Qed.

