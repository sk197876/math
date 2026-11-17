(** General norm topology supporting Federer (1969), 3.4.9,
    p. 337: every sufficiently small closed ball lies
    in each of finitely many original neighbourhoods. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import RealNormUP NormMetric NormDifferentialUP NormBoundedLinearTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [finite_norm_common_closed_ball]: the common
    small-radius choice for all original Vi in
    3.4.9, p. 337. The finite family may
    be empty, and the ambient dimension may be zero. *)
Theorem finite_norm_common_closed_ball (R:realType) (X:lmodType R)
    (NX:X->R) (hNX:is_real_norm NX) (I:finType) (U:set X) (V:I->set X):
  @open (real_norm_metric_space hNX) U ->U 0 ->
  (forall i,@open (real_norm_metric_space hNX) (V i) /\V i 0) ->
  exists rho:R,0<rho /\forall r,0<r ->r<rho ->
    forall x,NX x<=r ->U x /\forall i,V i x.
Proof.
move=>hU hU0 hV.
have hNearU:nbhs (0:real_norm_metric_space hNX) U.
  by move:hU;rewrite openE=>h;exact:h 0 hU0.
have hNearV i:nbhs (0:real_norm_metric_space hNX) (V i).
  have [hOpen hZero]:=hV i;move:hOpen;rewrite openE=>h;exact:h 0 hZero.
have hAll:=@filter_forall (real_norm_metric_space hNX) I (fun i x=>V i x)
  (nbhs (0:real_norm_metric_space hNX)) (nbhs_filter (0:real_norm_metric_space hNX)) hNearV.
have hBoth:nbhs (0:real_norm_metric_space hNX) [set x|U x /\forall i,V i x].
  exact:filterI hNearU hAll.
have [rho [hRho hInside]]:=(@norm_domain_interior_neighbourhood R X NX hNX
  [set x|U x /\forall i,V i x] 0).2 hBoth.
exists rho;split;first exact:hRho.
move=>r hR hUpper x hx;have h:=hInside x (le_lt_trans hx hUpper).
by rewrite add0r in h.
Qed.
