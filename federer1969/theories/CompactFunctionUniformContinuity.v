(** Federer (1969), 4.1.18, p. 375: compact
    continuous scalar functions have one modulus for
    all small translations. This supporting consequence
    of 2.2.5 and 2.2.7 also covers zero functions
    and empty supports.  *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals topology.
From Federer Require Import RealMetricBackground CompactSupportFunctionUP
  CompactNearbyUniformContinuity RealNormUP NormMetric.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [compact_function_uniform_continuity]:
    the compact-function uniformity used to choose
    the nearby-translate majorant in Federer 4.1.18,
    p. 375. Outside the support both values vanish;
    otherwise compact-base uniformity applies. *)
Theorem compact_function_uniform_continuity (R:realType)
    (X:metricType R) (f:X->R):
  compactly_supported_continuous_functions f ->
  forall e:R,0<e -> exists d:R,0<d /\
    forall x y:X,mdist x y<d -> `|f y-f x|<e.
Proof.
move=>hF e he.
have hAt c:real_function_support f c ->forall t:R,0<t ->
    exists r:R,0<r /\forall y:X,setT y ->
      mdist c y<r ->mdist (f c:real_line_metric R) (f y)<t.
  move=>_ t ht.
  have hBall:nbhs (f c:real_line_metric R)
      [set v|mdist (f c:real_line_metric R) v<t].
    apply:(proj2 (metricType_numDomainType.nbhs_mdistP
      (f c:real_line_metric R) _)).
    by exists t=>// v hv.
  have hPre:nbhs c [set y:X|mdist (f c:real_line_metric R) (f y)<t]:=
    hF.1 c _ hBall.
  have [r hr hBound]:=proj1
    (metricType_numDomainType.nbhs_mdistP c _) hPre.
  by exists r; split=>// y _; exact:hBound.
have [d [hd hBound]]:=@metric_compact_uniform_nearby R X
  (real_line_metric R) setT (real_function_support f) f hF.2
  (fun _ _=>Logic.I) hAt e he.
exists d; split=>// x y hxy.
case:(pselect (real_function_support f x))=>[hx|hx].
- have h:=hBound x y hx Logic.I hxy.
  change (is_true (`|f x-f y|<e)) in h.
  by rewrite distrC.
- case:(pselect (real_function_support f y))=>[hy|hy].
  + have hyx:mdist y x<d by rewrite metric_sym.
    exact:(hBound y x hy Logic.I hyx).
  + rewrite (real_function_zero_off_support hx)
      (real_function_zero_off_support hy) subrr normr0.
    exact:he.
Qed.

(** Source for [compact_function_uniform_translation]:
    the preceding uniformity for the literal translations
    x maps to x+z in Federer 4.1.18, p. 375.
    No finite-dimensional or separability assumption is
    needed for this supporting statement. *)
Theorem compact_function_uniform_translation (R:realType)
    (X:lmodType R) (NX:X->R) (hNX:is_real_norm NX)
    (f:real_norm_metric_space hNX->R):
  compactly_supported_continuous_functions f ->
  forall e:R,0<e ->exists d:R,0<d /\
    forall z:X,NX z<d ->forall x:X,`|f (x+z)-f x|<e.
Proof.
move=>hF e he.
have [d [hd hBound]]:=@compact_function_uniform_continuity R
  (real_norm_metric_space hNX) f hF e he.
exists d; split=>// z hz x.
apply:hBound.
change (is_true (NX (x-(x+z))<d)).
by rewrite opprD addrA subrr add0r
  (real_seminorm_negate hNX.1).
Qed.
