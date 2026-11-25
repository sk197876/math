(** Private Archimedean existence proof for the positive integer subdivision
    count in Federer (1969), 2.10.45, pp. 202–203. For positive side length
    use the least natural covering multiple; for zero side use count one. No
    ceiling function is exposed downstream. Source context:
    UniformMeshCountUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra reals lra.
From Federer Require Import UniformMeshCountUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [uniform_mesh_count_exists]: supporting
    existence of the printed j(T) in
    2.10.45, pp. 202–203, with zero
    side length also allowed by the weak bracket. *)
Theorem uniform_mesh_count_exists (R : realType) (u h : R) :
  0<=u -> 0<h -> exists k, is_uniform_mesh_count u h k.
Proof.
move=> hu hh.
case: (ltP 0 u)=> [hupos|hu0]; last first.
  have -> : u=0 by apply/eqP; rewrite eq_le hu0 hu.
  exists 1%N; constructor=> //; rewrite mul1r ?add0r //; exact: ltW hh.
have hdiv : 0<=u/h by apply: divr_ge0; exact: ltW.
have hex : exists k : nat, u<=k%:R*h.
  exists (Num.bound (u/h)); rewrite -ler_pdivrMr //.
  exact: ltW (archi_boundP hdiv).
have [k hk hmin] := ex_minnP hex.
have hkpos : (0<k)%N.
  rewrite lt0n; apply/eqP=> hk0.
  by rewrite hk0 mul0r leNgt hupos in hk.
exists k; constructor=> //.
case: k hk hkpos hmin=> [|k] hk hkpos hmin; first by rewrite ltn0 in hkpos.
have hprev : k%:R*h<u.
  rewrite ltNge; apply/negP=> hc.
  have hn := hmin k hc; by rewrite leqNgt ltnSn in hn.
rewrite -addn1 natrD mulrDl mul1r; lra.
Qed.
