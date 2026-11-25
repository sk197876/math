(** Federer (1969), 4.1.8, p. 362: the
    original scalar segment is integration over the
    ordered open interval. Reuse affine Lebesgue
    transport, finite integral scaling and the null
    endpoint replacement already proved in Chapter 2. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets
  reals constructive_ereal topology normedtype ring lra.
From Federer Require Import RealMetricBackground ExtendedRealOrderTopology LebesgueScalarMeasure
  ScalarAffinePushforward ScalarRectangleAffine ScaledSubsetIntegralTransport PartialFunctionUP PartialFunctionPrecomposition PartialZeroExtension
  MeasureUP MeasureAlmostUP MeasureAlmostBasic MeasureFiniteClosure MeasureIntegralUP MeasureSubsetIntegral
  MeasureIntegralGraphEquivalence SubsetIntegralNullReplacement RealSubsetFiniteScale SummableRealFunctionUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory numFieldTopology.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [scalar_open_closed_interval_integral]: restoring
    the two null endpoints preserves the original
    scalar interval integral, supporting Federer 4.1.8,
    p. 362, by 2.4.3(2), p. 81, and
    2.5.17, p. 111. Partial integrands and
    arbitrary signed integral values are retained. *)
Lemma scalar_open_closed_interval_integral (R:realType)
    (f:partial_function (real_line_metric R) (extended_real_line R)) u v a:
  is_measure_subset_integral (@lebesgue_scalar_measure R) `]u,v[ f a ->
  is_measure_subset_integral (@lebesgue_scalar_measure R) `[u,v] f a.
Proof.
move=>hIntegral.
have hNull:lebesgue_scalar_measure ([set u] `|` [set v])=0%E.
  exact:(@measure_null_union R R (@lebesgue_scalar_measure R) (lebesgue_scalar_is_measure R)
    [set u] [set v] (@lebesgue_scalar_singleton R u) (@lebesgue_scalar_singleton R v)).
apply:(@subset_integral_null_replacement R (real_line_metric R) (@lebesgue_scalar_measure R)
  f `]u,v[ `[u,v] ([set u] `|` [set v]) a (lebesgue_scalar_is_measure R) hNull _ hIntegral).
move=>x hx.
have hxu:x!=u by apply/eqP=>h;apply:hx;left;exact:h.
have hxv:x!=v by apply/eqP=>h;apply:hx;right;exact:h.
rewrite /mkset !in_itv /= (lt_neqAle u x) eq_sym hxu (lt_neqAle x v) hxv /=.
by [].
Qed.

(** Source for [scalar_positive_affine_segment_integral]:
    the original substitution s=(1-t)u+t v
    identifies the segment's velocity-weighted [0,1]
    integral with the ordered interval integral,
    supporting the final display of Federer 4.1.8,
    p. 362. No continuity hypothesis is added
    to an already integrable scalar function. *)
Theorem scalar_positive_affine_segment_integral (R:realType) (f:R->R) u v a:
  u<v->is_measure_subset_integral (@lebesgue_scalar_measure R) `]u,v[
    (real_total_integrand f) a%:E ->
  is_measure_subset_integral (@lebesgue_scalar_measure R) `[0,1]
    (real_total_integrand (fun t=>(v-u)*f ((v-u)*t+u))) a%:E.
Proof.
move=>huv hIntegral.
pose r:=v-u.
pose F (t:real_line_metric R):real_line_metric R:=r*t+u.
have hr:0<r by rewrite /r subr_gt0.
have hrNe:r!=0 by rewrite (gt_eqF hr).
have hInj:injective F.
  move=>s t h;have h':r*s=r*t:=addIr u h.
  exact:(mulfI hrNe h').
have hPush:=@scalar_affine_pushforward_measure R r u hrNe.
rewrite (ger0_norm (ltW hr)) in hPush.
have hClosed:=scalar_open_closed_interval_integral hIntegral.
have hPull:=@scaled_subset_integral_transport R (real_line_metric R) (real_line_metric R)
  (@lebesgue_scalar_measure R) (@lebesgue_scalar_measure R)
  (lebesgue_scalar_is_measure R) (lebesgue_scalar_is_measure R) F r^-1 `[u,v]
  (real_total_integrand f) a%:E hInj (ltac:(by rewrite invr_gt0)) hPush hClosed.
have hPre:F @^-1` (`[u,v]:set (real_line_metric R))=(`[0,1]:set (real_line_metric R)).
  apply:funext=>t;apply:propext.
  change ((r*t+u \in `[u,v]%R) <-> (t \in `[0,1]%R)).
  have h0:u+r*0=u by ring.
  have h1:u+r*1=v by rewrite /r;ring.
  have hTest:=@positive_affine_interval_test R u r 0 1 t true false hr.
  rewrite h0 h1 [u+r*t]addrC in hTest.
  by rewrite hTest.
rewrite hPre -EFinM in hPull.
have hActual:is_measure_subset_integral (@lebesgue_scalar_measure R) `[0,1]
    (real_total_integrand (fun t=>f (F t))) (r^-1*a)%:E.
  apply:(measure_integral_graph_equivalent _ hPull)=>t z.
  have hInner:partial_function_graph (partial_function_precompose F (real_total_integrand f)) t z <->
      partial_function_graph (real_total_integrand (fun t=>f (F t))) t z.
    change (partial_function_graph (real_total_integrand f) (F t) z <->
      partial_function_graph (real_total_integrand (fun t=>f (F t))) t z).
    by rewrite !real_total_integrand_graph.
  by rewrite !partial_function_zero_extension_graph hInner.
have hScaled:=@real_subset_integral_multiply_finite_scale R (real_line_metric R)
  (@lebesgue_scalar_measure R) (lebesgue_scalar_is_measure R) `[0,1]
  (fun t=>r*f (F t)) (fun t=>f (F t)) (r^-1*a) r hrNe (fun _ _=>erefl) hActual.
by rewrite mulrA mulfV // mul1r in hScaled.
Qed.
