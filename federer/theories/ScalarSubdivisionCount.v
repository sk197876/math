(** Federer (1969), 2.10.39, printed p. 199: choose positive integers k_i
    with k_i/2<c_i/c_m<=k_i. The supporting Archimedean argument below
    chooses the least natural multiple of a positive mesh above a length at
    least that mesh. This proves existence rather than defining a ceiling
    operation. *)
From mathcomp Require Import all_boot all_order all_algebra reals lra.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [positive_mesh_subdivision_count]: supporting
    integer choice in 2.10.39, p. 199.
    In words, a length at least one positive mesh
    admits a positive count whose mesh multiple covers
    the length and is strictly less than twice it. *)
Lemma positive_mesh_subdivision_count (R : realType) (c h : R) :
  0<h -> h<=c -> exists k : nat,
    (0<k)%N /\ c<=k%:R*h /\ k%:R*h<2*c.
Proof.
move=> hh hhc.
have hc : 0<c := lt_le_trans hh hhc.
have hd : 0<=c/h by apply: divr_ge0; exact: ltW.
have hex : exists k : nat, c<=k%:R*h.
  exists (Num.bound (c/h)); rewrite -ler_pdivrMr //.
  exact: ltW (archi_boundP hd).
have [k hk hmin] := ex_minnP hex.
have hk0 : (0<k)%N.
  rewrite lt0n; apply/eqP=> hz.
  by rewrite hz mul0r leNgt hc in hk.
exists k; split=> //; split=> //.
case: k hk hk0 hmin=> [|k] hk hk0 hmin; first by rewrite ltn0 in hk0.
have hprev : k%:R*h<c.
  rewrite ltNge; apply/negP=> hb.
  have hn := hmin k hb; by rewrite leqNgt ltnSn in hn.
have he : k.+1%:R*h=k%:R*h+h by rewrite -addn1 natrD mulrDl mul1r.
rewrite he; lra.
Qed.
