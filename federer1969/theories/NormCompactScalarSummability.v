(** Federer (1969), 4.1.1, p. 346: a
    continuous scalar function with a compact
    support bound has a finite integral. This
    is the already proved K(X) summability
    argument of 2.5.13 and 2.7.16. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric RealMetricBackground NormClassOneUP NormClassZeroTopology
  ScalarNormExtendedEmbedding CompactSupportFunctionUP SmoothCompactSet CompactSupportSummability
  TopologicalBorel MeasureUP MeasureIntegralUP SummableRealFunctionUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [norm_compact_scalar_summable]: a
    class-zero scalar function vanishing off a
    compact K is summable, supporting the
    integral derivative in Federer 4.1.1, p. 346. *)
Theorem norm_compact_scalar_summable (R:realType) (X:lmodType R)
    (NX:X->R) (hNX:is_real_norm NX) (mu:set X->\bar R) (hm:is_measure mu)
    (hB:forall A:set X,@borel_set (real_norm_metric_space hNX) A ->measure_measurable mu A)
    (hK:forall C:set X,@compact (real_norm_metric_space hNX) C ->(mu C< +oo)%E)
    (K:smooth_compact_set hNX (fun _=>True)) (f:X->R):
  norm_class_zero NX (fun t:R^o=>`|t|) (fun _=>True) f ->
  (forall x,~smooth_compact_carrier K x ->f x=0) ->
  exists a:R,is_measure_integral mu (real_total_integrand f) a%:E.
Proof.
move=>hF hZero.
pose T:=real_norm_metric_space hNX.
have hNorm:continuous (fun x:T=>(f x:real_norm_metric_space (@scalar_absolute_value_norm R))).
  move=>x; exact:(@norm_class_zero_continuous_at R X R^o NX (fun t:R^o=>`|t|) hNX
    (@scalar_absolute_value_norm R) (fun _=>True) f x hF Logic.I).
have hReal:continuous (fun x:T=>(f x:real_line_metric R)).
  move=>x; exact:(continuous_comp (hNorm x) (@ScalarNormExtendedEmbedding.scalar_norm_real_identity_continuous R _)).
have hClosed:=compact_closed (@metric_hausdorff R T) (smooth_compact_is_compact K).
have hSupport:@real_function_support R T f `<=` smooth_compact_carrier K.
  have hSub:[set x:T|f x<>0] `<=` smooth_compact_carrier K.
    move=>x hx; case:(pselect (smooth_compact_carrier K x))=>// hn.
    exact:False_ind _ (hx (hZero x hn)).
  have h:=closureS hSub.
  by rewrite -((closure_id _).1 hClosed) in h.
have hEq:@real_function_support R T f=smooth_compact_carrier K `&` @real_function_support R T f.
  apply:funext=>x; apply:propext; split; first by move=>hx; split=>//; exact:hSupport.
  by move=>[].
have hCompact:@compact T (@real_function_support R T f).
  rewrite hEq; exact (@compact_closedI T (smooth_compact_carrier K) (@real_function_support R T f)
    (smooth_compact_is_compact K) (@real_function_support_closed R T f)).
exact:(@compactly_supported_summable R T mu hm hB hK f (conj hReal hCompact)).
Qed.
