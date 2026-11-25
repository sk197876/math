(** Federer (1969), 3.1.21, p. 234: tangent cones depend
    only on the set in a neighbourhood of their base point. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals.
From Federer Require Import NormDifferentialUP TangentConeUP TangentConeClosure.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [norm_tangent_open_restriction]: supporting the
    local straightening and constant-rank fibre arguments of
    Federer 3.1.21, p. 234. Intersecting S with any
    neighbourhood of a leaves Tan(S,a) unchanged. *)
Lemma norm_tangent_open_restriction (R:realType) (X:lmodType R)
    (N:X->R) (S A:set X) a : norm_domain_interior N A a ->
  norm_tangent_cone N (S `&` A) a=norm_tangent_cone N S a.
Proof.
move=>[r [hr hA]].
apply: (@norm_tangent_local_agreement R X N (S `&` A) S a r hr)=>x hx.
have hAx:A x by have hh:=hA (x-a) hx; rewrite addrC subrK in hh.
split; first by move=>[hs _].
move=>hs; exact (conj hs hAx).
Qed.
