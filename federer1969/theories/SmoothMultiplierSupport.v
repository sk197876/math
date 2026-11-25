(** Federer (1969), 4.1.1, pp. 344–345: multiplication
    shrinks function supports and preserves compact-support
    subspaces. These arguments use the original closure
    definition and the public product evaluation law. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormMetric CompactSupportFunctionUP SmoothCompactSet
  SmoothFunctionSpaceUP SmoothFunctionSupport SmoothMultiplierUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section MultiplierSupport.
Variable R:realType.
Variables X Y:lmodType R.
Variables (NX:X->R) (NY:Y->R).
Hypothesis hNX:is_real_norm NX.
Hypothesis hNY:is_real_norm NY.
Variable U:set X.
Variable E:lmodType R.
Variable ev:E->X->Y.
Hypothesis hE:is_smooth_function_space hNX hNY U ev.
Variable u:X->R.
Variable P:Hom E E.
Hypothesis hP:is_smooth_multiplier U ev u P.
Local Notation XN := (real_norm_metric_space hNX).
Local Notation support := (@smooth_function_support R X Y NX hNX U E ev).

(** Source for [smooth_multiplier_support_subset]: spt(u phi)
    is contained in spt phi, supporting the local restrictions
    in Federer 4.1.1, p. 345. *)
Lemma smooth_multiplier_support_subset f:support (P f) `<=` support f.
Proof.
move=>x [hx hCl]; split=>//.
apply:(@closureS XN [set y|ev (P f) y<>0] [set y|ev f y<>0] _ x hCl)=>y hn hy.
change (ev (P f) y<>0) in hn.
case:(pselect (U y))=>[hu|hu].
- by move:hn; rewrite (hP f hu) hy scaler0.
- exact:hn (smooth_function_evaluation_outside hE (P f) hu).
Qed.

(** Source for [smooth_multiplier_scalar_support_subset]:
    spt(u phi) is contained in the actual scalar support,
    supporting the compact cutoff operations in Federer
    4.1.1, pp. 344–345. *)
Lemma smooth_multiplier_scalar_support_subset f:
  support (P f) `<=` @real_function_support R XN u.
Proof.
move=>x [hx hCl].
apply:(@closureS XN [set y|ev (P f) y<>0] [set y|u y<>0] _ x hCl)=>y hn hy.
change (ev (P f) y<>0) in hn.
case:(pselect (U y))=>[hu|hu].
- by move:hn; rewrite (hP f hu) hy scale0r.
- exact:hn (smooth_function_evaluation_outside hE (P f) hu).
Qed.

(** Source for [smooth_multiplier_preserves_compact_support]:
    multiplication preserves every D_K, supporting T L v_s
    in Federer 4.1.1, p. 345. *)
Theorem smooth_multiplier_preserves_compact_support
    (K:smooth_compact_set hNX U) f:
  support f `<=` smooth_compact_carrier K ->
  support (P f) `<=` smooth_compact_carrier K.
Proof. move=>hf x hx; exact:(hf x (@smooth_multiplier_support_subset f x hx)). Qed.

(** Source for [smooth_multiplier_compact_scalar_support]:
    a compactly supported scalar sends all E functions into
    one fixed D_K, supporting the compact-support dual
    extension in Federer 4.1.1, p. 345. *)
Theorem smooth_multiplier_compact_scalar_support
    (K:smooth_compact_set hNX U):
  @real_function_support R XN u `<=` smooth_compact_carrier K ->
  forall f,support (P f) `<=` smooth_compact_carrier K.
Proof. move=>hu f x hx; exact:(hu x (@smooth_multiplier_scalar_support_subset f x hx)). Qed.
End MultiplierSupport.
