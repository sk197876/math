(** Federer (1969), 4.1.7, pp. 358–359:
    a scalar majorant controls the support of
    an original test. This is a supporting
    consequence of the norm and closure definitions
    from 4.1.1, p. 344. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import RealNormUP NormMetric CompactSupportFunctionUP SmoothFunctionSupport.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [norm_dominated_function_support]:
    a pointwise scalar norm bound places the
    original function support in the majorant's
    support, supporting the normality and proper
    pushforward arguments in Federer 4.1.7,
    pp. 358–359. No continuity of the
    majorant is needed for this inclusion. *)
Theorem norm_dominated_function_support (R:realType) (X Y:lmodType R)
    (NX:X->R) (NY:Y->R) (hNX:is_real_norm NX) (hNY:is_real_norm NY)
    (U:set X) (E:lmodType R) (ev:E->X->Y) (phi:E) (g:X->R):
  (forall x,NY (ev phi x)<=g x)->
  @smooth_function_support R X Y NX hNX U E ev phi `<=`
    @real_function_support R (real_norm_metric_space hNX) g.
Proof.
move=>hBound x [hx hClosure].
apply:(@closureS (real_norm_metric_space hNX) _ _ _ x hClosure)=>z hz hZero.
have hNormZero:NY (ev phi z)=0.
  apply/eqP;rewrite eq_le (real_seminorm_nonnegative hNY.1 _) andbT.
  by rewrite -hZero;exact:hBound z.
exact:hz (hNY.2 _ hNormZero).
Qed.
