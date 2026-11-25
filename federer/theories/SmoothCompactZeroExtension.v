(** Federer (1969), 4.1.1, p. 345: a compactly supported
    smooth function on U extends smoothly by zero. The proof
    reuses local gluing of class-k maps from 3.1.11 and 3.1.20. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP NormBoundedLinearTopology
  NormRegularity NormRegularityOperations NormRegularityLocal SmoothCompactSet
  SmoothFunctionSpaceUP SmoothFunctionSupport.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section CompactZeroExtension.
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

(** Source for [smooth_compact_zero_extension_regular]: the
    normalized total representative of a compactly supported
    smooth function is smooth on the whole source, supporting
    the zero-extension monomorphism in Federer 4.1.1, p. 345.
    Values on U are unchanged and values outside U are zero. *)
Theorem smooth_compact_zero_extension_regular (K:smooth_compact_set hNX U) f:
  support f `<=` smooth_compact_carrier K ->
  norm_class_all_orders hNX hNY (@setT X) (ev f).
Proof.
move=>hf k; apply:norm_class_local_representatives=>x hx.
case:(pselect (U x))=>[hUx|hUx].
- exists U,(ev f); split=>//; split; first by move=>y hy.
  split; first exact:smooth_function_evaluation_smooth hE f k.
  by move=>y hy.
- pose O:set X:=[set y|~smooth_compact_carrier K y].
  have hKClosed:=compact_closed (@metric_hausdorff R (real_norm_metric_space hNX))
    (smooth_compact_is_compact K).
  have hOpen:=closed_openC hKClosed.
  have hInterior y (hy:O y):norm_domain_interior NX O y.
    apply:(norm_domain_interior_neighbourhood hNX O y).2.
    by move:hOpen; rewrite openE; apply.
  exists O,(fun _=>0); split.
  + move=>hKx; exact:hUx (smooth_compact_in_domain K x hKx).
  + split; first by move=>y hy.
    split; first exact:(@norm_class_constant R X Y NX NY hNX hNY O 0 k hInterior).
    move=>y hy; symmetry; exact:((smooth_function_compact_support_iff hE K f).1 hf y hy).
Qed.
End CompactZeroExtension.
