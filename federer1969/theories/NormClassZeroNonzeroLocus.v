(** Federer (1969), 3.1.24, p. 240: the root
    set of an analytic function on an open Euclidean domain
    is measurable. Its complement relative to the domain is open. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import RealNormUP NormMetric NormDifferentialUP NormClassOneUP
  NormBoundedLinearTopology NormClassZeroTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [norm_class_zero_nonzero_locus_open]: supporting
    the measurability of the zero set in Federer 3.1.24,
    p. 240. For a continuous map on an open domain,
    the locus where its norm is positive is open, by a
    ball of radius less than the nonzero value's norm. *)
Theorem norm_class_zero_nonzero_locus_open (R:realType) (X Y:lmodType R)
    (NX:X->R) (NY:Y->R) (hNX:is_real_norm NX) (hNY:is_real_norm NY)
    (A:set X) (f:X->Y) :
  norm_class_zero NX NY A f ->
  @open (real_norm_metric_space hNX) (fun x=>A x /\ f x!=0).
Proof.
move=>hf; rewrite openE=>a [ha hn].
have hp:0<NY (f a) by rewrite (real_norm_positive hNY.1 hNY.2) hn.
have [r [hr hb]]:=@norm_class_zero_local_control R X Y NX NY hNX A f a (NY (f a)) hf ha hp.
apply: (proj1 (@norm_domain_interior_neighbourhood R X NX hNX (fun x=>A x /\ f x!=0) a)).
exists r; split; first exact hr.
move=>v hv.
have hsmall:NX ((a+v)-a)<r by rewrite addrAC subrr add0r.
have [hav hrem]:=hb (a+v) hsmall.
split; first exact hav.
apply/eqP=>hz.
by rewrite hz sub0r (real_seminorm_negate hNY.1) ltxx in hrem.
Qed.
