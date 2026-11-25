(** Federer (1969), 4.1.3, p. 348: every original
    one-variable test has bounded support. This supplies the
    compact coordinate box for the canonical product test.
    The bound follows from the earlier compact norm bound. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets reals topology.
From Federer Require Import Hom TensorUP RealNormUP NormMetric NormDifferentialUP
  NormOpenDomainLaws NormRegularity NormRegularityOperations NormCompactFunctionBound
  SmoothCompactSet SmoothFunctionSpaceUP SmoothFunctionSupport SmoothTestSpaces SmoothTestEvaluation.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [test_line_nonzero_argument_bound]: boundedness of
    the actual one-variable support, supporting the coordinate
    products in Federer 4.1.3, p. 348. *)
Theorem test_line_nonzero_argument_bound (R:realType) (A:lmodType R)
    (av:A->R^o->R^o)
    (hA:is_smooth_function_space (@scalar_absolute_value_norm R)
      (@scalar_absolute_value_norm R) (fun _=>True) av) (f:smooth_test_space hA):
  exists b:R,0<b /\ forall t:R,smooth_test_value hA f t<>0 ->`|t|<=b.
Proof.
pose hR:=@scalar_absolute_value_norm R.
have[K hK]:=smooth_test_support_bound hA f.
have hIdBound:norm_bounded_linear (fun t:R^o=>`|t|) (fun t:R^o=>`|t|)
    (hom_of_linear (linear_id R^o)).
  exists 1; split; first exact:ler01; by move=>t; rewrite mul1r.
have hId:=@norm_class_linear R R^o R^o _ _ hR hR (fun _=>True)
  (hom_of_linear (linear_id R^o)) 0%N (fun x _=>norm_full_domain_interior _ x) hIdBound.
have[b [hb hBound]]:=@norm_class_zero_compact_bounded R R^o R^o _ _ hR hR
  (fun _=>True) (smooth_compact_carrier K) (fun t=>t) (smooth_compact_is_compact K)
  (fun _ _=>I) (norm_class_continuous hId).
exists b; split=>// t ht; apply:hBound; apply:hK.
split; first exact I.
exact:(@subset_closure (real_norm_metric_space hR)
  [set z|smooth_test_value hA f z<>0] t ht).
Qed.
