(** Federer (1969), 4.1.1, pp. 344–345: fixed compact support
    and compact support specify linear subspaces of E(U,Y).
    The predicates use the original support definition. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import Hom ModuleQuotient RealNormUP SmoothCompactSet SmoothFunctionSpaceUP
  SmoothFunctionSpaceLaws SmoothFunctionSupport.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section TestSubspaces.
Variable R:realType.
Variables X Y:lmodType R.
Variables (NX:X->R) (NY:Y->R).
Hypothesis hNX:is_real_norm NX.
Hypothesis hNY:is_real_norm NY.
Variable U:set X.
Variable E:lmodType R.
Variable ev:E->X->Y.
Hypothesis hE:is_smooth_function_space hNX hNY U ev.
Local Notation support := (@smooth_function_support R X Y NX hNX U E ev).

(** Source for [smooth_fixed_support_subspace]: the predicate
    spt phi contained in K is a linear subspace, defining D_K(U,Y)
    in Federer 4.1.1, p. 344. *)
Definition smooth_fixed_support_subspace (K:smooth_compact_set hNX U):subspace E.
Proof.
refine (@Subspace R E (fun f=>support f `<=` smooth_compact_carrier K) _ _ _).
- apply:(smooth_function_compact_support_iff hE K 0).2=>x hx.
  exact:(smooth_function_zero_value hE x).
- move=>f g hf hg; apply:(smooth_function_compact_support_iff hE K (f+g)).2=>x hx.
  rewrite (smooth_function_add_value hE)
    ((smooth_function_compact_support_iff hE K f).1 hf x hx)
    ((smooth_function_compact_support_iff hE K g).1 hg x hx) addr0; reflexivity.
- move=>c f hf; apply:(smooth_function_compact_support_iff hE K (c*:f)).2=>x hx.
  by rewrite (smooth_function_scale_value hE)
    ((smooth_function_compact_support_iff hE K f).1 hf x hx) scaler0.
Defined.

(** Source for [smooth_compact_support_subspace]: the union of
    all fixed-support spaces is a linear subspace, defining D(U,Y)
    in Federer 4.1.1, p. 344. Finite sums use unions of compact sets. *)
Definition smooth_compact_support_subspace:subspace E.
Proof.
refine (@Subspace R E
  (fun f=>exists K:smooth_compact_set hNX U,support f `<=` smooth_compact_carrier K) _ _ _).
- exists (@smooth_compact_empty R X NX hNX U).
  exact:(subspace_zero (smooth_fixed_support_subspace _)).
- move=>f g [K hK] [L hL]; exists (smooth_compact_union K L).
  apply:(smooth_function_compact_support_iff hE _ (f+g)).2=>x hx.
  have hxK:~smooth_compact_carrier K x by move=>hk; apply:hx; left.
  have hxL:~smooth_compact_carrier L x by move=>hl; apply:hx; right.
  by rewrite (smooth_function_add_value hE)
    ((smooth_function_compact_support_iff hE K f).1 hK x hxK)
    ((smooth_function_compact_support_iff hE L g).1 hL x hxL) addr0.
- move=>c f [K hK]; exists K; exact:(@subspace_scale R E (smooth_fixed_support_subspace K) c f hK).
Defined.
End TestSubspaces.
