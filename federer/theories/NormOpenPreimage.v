(** General topology supporting the open-image assertion in
    Federer (1969), 3.1.19(4) implies (3), p. 231. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals topology.
From Federer Require Import RealNormUP NormMetric NormDifferentialUP
  NormClassOneUP NormClassZeroTopology NormBoundedLinearTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [norm_class_zero_open_preimage]: the ambient open
    set T intersect phi inverse(W) used in the proof of (4) implies
    (3), Federer 3.1.19, p. 231. Supporting topology lemma. *)
Lemma norm_class_zero_open_preimage (R:realType) (X Y:lmodType R)
    (NX:X->R) (NY:Y->R) (hNX:is_real_norm NX) (hNY:is_real_norm NY)
    (T:set X) (W:set Y) (f:X->Y) : norm_class_zero NX NY T f ->
  @open [the topologicalType of real_norm_metric_space hNY] W ->
  @open [the topologicalType of real_norm_metric_space hNX] [set x|T x /\ W (f x)].
Proof.
move=>hf hW; rewrite openE=>x [hx hw].
apply: (proj1 (@norm_domain_interior_neighbourhood R X NX hNX _ x)).
have [s [hs hball]]:=proj2 (@norm_domain_interior_neighbourhood R Y NY hNY W (f x))
  (open_nbhs_nbhs (conj hW hw)).
have [r [hr hcontrol]]:=@norm_class_zero_local_control R X Y NX NY hNX T f x s hf hx hs.
exists r; split=>// h hh.
have hxc:NX (x+h-x)<r by rewrite (addrC x h) addrK.
have [hT hsmall]:=hcontrol (x+h) hxc; split=>//.
have hw':=hball (f (x+h)-f x) hsmall.
by rewrite addrC subrK in hw'.
Qed.
