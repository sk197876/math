(** Federer (1969), 4.1.5, p. 350:
    countably many compact interior neighbourhoods
    suffice for the local ball formula. Reuse
    the independently specified compact exhaustion
    already proved in 4.1.1; its neighbourhood
    law applied to singletons covers every point. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import RealNormUP NormMetric SmoothCompactSet SmoothCompactExhaustionUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [smooth_compact_exhaustion_interior_cover]: the
    countable interior cover used to assemble
    the original almost-everywhere ball formula,
    Federer 4.1.5, p. 350. Empty
    domains need no inhabited-source premise. *)
Theorem smooth_compact_exhaustion_interior_cover (R:realType) (X:lmodType R)
    (NX:X->R) (hNX:is_real_norm NX) (U:set X)
    (K:nat->smooth_compact_set hNX U) (hK:is_smooth_compact_exhaustion K):
  forall x,U x ->exists j,@interior (real_norm_metric_space hNX) (smooth_compact_carrier (K j)) x.
Proof.
move=>x hX.
have hSubset:([set x]:set X) `<=` U.
  move=>z hZ; change (z=x) in hZ; by rewrite hZ.
pose C:=@Build_smooth_compact_set R X NX hNX U [set x] hSubset
  (@compact_set1 (real_norm_metric_space hNX) x).
have[j [W [hOpen [hCW hWK]]]]:=smooth_compact_exhaustion_neighbourhood hK C.
exists j.
have hXW:W x:=hCW x (erefl x).
have hNeighbourhood:nbhs (x:real_norm_metric_space hNX) W.
  exact:open_nbhs_nbhs (conj hOpen hXW).
exact:(filterS hWK hNeighbourhood).
Qed.
