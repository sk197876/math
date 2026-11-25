(** Federer (1969), 4.1.1, p. 345: the same
    compact K is a fixed-support index in any larger
    open domain. This supporting transport changes no
    underlying point or compact-set carrier. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals.
From Federer Require Import RealNormUP SmoothCompactSet.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Source for [smooth_compact_domain_inclusion]: retain
    the original K under U contained in V, as in
    D_K(U,Y) and D_K(V,Y) of Federer 4.1.1,
    p. 345. *)
Definition smooth_compact_domain_inclusion (R:realType) (X:lmodType R)
    (NX:X->R) (hNX:is_real_norm NX) (U V:set X) (hUV:forall x,U x ->V x)
    (K:smooth_compact_set hNX U):smooth_compact_set hNX V:=
  @Build_smooth_compact_set R X NX hNX V (smooth_compact_carrier K)
    (fun x hx=>@hUV x (smooth_compact_in_domain K x hx)) (smooth_compact_is_compact K).
