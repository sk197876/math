(** Federer (1969), 3.4.11, p. 338:
    original tangent vectors remain in a closed set
    containing every positive dilation of the original source.
    Reuse the metric closure characterization already used
    in the closed-subspace tangent theorem of 3.1.21. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals topology.
From Federer Require Import RealNormUP NormMetric NormClosureBalls TangentConeUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [norm_tangent_closed_dilation_containment]:
    the nonnegative first-coordinate restriction for the cusp
    tangent in 3.4.11, p. 338, follows
    from the original tangent definition and closedness.
    No convexity or vector-subspace hypothesis is required. *)
Theorem norm_tangent_closed_dilation_containment (R:realType) (X:lmodType R)
    (NX:X->R) (hNX:is_real_norm NX) (S C:set X):
  @closed (real_norm_metric_space hNX) C ->
  (forall x,S x ->forall t:R,0<t ->C (t*:x)) ->
  norm_tangent_cone NX S 0 `<=` C.
Proof.
move=>hClosed hContain v hTangent.
apply:hClosed;apply:(@norm_closure_balls R X NX hNX C v).2=>e he.
have [x [t [hx [ht [hX hV]]]]]:=hTangent e he.
rewrite subr0 in hV.
exists (t*:x);split;[exact:hContain x hx t ht|exact:hV].
Qed.
