(** Federer (1969), 4.1.7, p. 359:
    a fixed smooth map carries each
    original compact source index to a
    compact target index. This supports the
    finite seminorm estimate for pullback. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals topology.
From Federer Require Import RealNormUP NormMetric NormClassOneUP NormClassZeroTopology SmoothCompactSet.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [smooth_compact_image]: the
    original compact image f(K) inside
    the target domain, supporting the
    pullback in Federer 4.1.7,
    p. 359. *)
Definition smooth_compact_image (R:realType) (X Y:lmodType R)
    (NX:X->R) (NY:Y->R) (hNX:is_real_norm NX) (hNY:is_real_norm NY)
    (A:X->Prop) (B:Y->Prop) (f:X->Y)
    (hImage:forall x,A x->B (f x)) (hf:norm_class_zero NX NY A f)
    (K:smooth_compact_set hNX A):smooth_compact_set hNY B.
Proof.
refine (@Build_smooth_compact_set R Y NY hNY B (f @` smooth_compact_carrier K) _ _).
- move=>y [x hx <-];exact:(@hImage x (smooth_compact_in_domain K x hx)).
- apply:continuous_compact (smooth_compact_is_compact K).
  apply:continuous_in_subspaceT=>x hx.
  have hKx:smooth_compact_carrier K x:=set_mem hx.
  exact:(@norm_class_zero_continuous_at R X Y NX NY hNX hNY A f x hf
    (smooth_compact_in_domain K x hKx)).
Defined.
