(** General topology supporting the convex analytic coordinate
    domains used in Federer (1969), 3.2.33, p. 270,
    through 3.1.19(4) and 3.1.24, pp. 231,240. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets set_interval
  reals topology normed_module.
From Federer Require Import RealNormUP NormMetric InnerConvex RealMetricBackground
  NormMetricScaleContinuity NormClosureLaws.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory numFieldTopology.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [norm_inner_convex_connected]: the connected
    coordinate domains in the analytic rank-set argument of
    Federer 3.2.33, p. 270. A convex set is the
    union of segments from one point; those segments are
    continuous images of the real unit interval and intersect
    at that point. The empty set is included. *)
Theorem norm_inner_convex_connected (R:realType) (X:lmodType R)
    (N:X->R) (hN:is_real_norm N) (A:set X):
  is_inner_convex A ->@connected (real_norm_metric_space hN) A.
Proof.
move=>hConvex.
case:(pselect (exists a,A a))=>[[a ha]|hEmpty].
- pose M:=real_norm_metric_space hN.
  pose P (x:M):set M:=(fun t:real_line_metric R=>a+t*:(x-a)) @` `[0,1].
  have hP x:connected (P x).
    apply:connected_continuous_connected; first exact:segment_connected.
    apply:continuous_subspaceT=>t.
    exact:(continuous_comp (@real_norm_metric_scalar_orbit_continuous R X N hN (x-a) t)
      (@real_norm_metric_translate_continuous R X N hN a (t*:(x-a)))).
  have hCommon:(\bigcap_(x in A) P x)!=set0.
    exists a=>x hx; exists (0:R); last by rewrite scale0r addr0.
    by rewrite set_itvcc /= lexx ler01.
  have hImage:A=\bigcup_(x in A) P x.
    apply/seteqP; split=>x hx.
    + exists x; first exact hx; exists (1:R); last by rewrite scale1r addrC subrK.
      by rewrite set_itvcc /= ler01 lexx.
    + have [y hy [t ht <-]]:=hx.
      have /andP[ht0 ht1]:=ht.
      have hFormula:a+t*:(y-a)=(1-t)*:a+t*:y.
        by rewrite scalerBr scalerBl scale1r addrA addrAC.
      rewrite hFormula; exact:(hConvex a y ha hy t ht0 ht1).
  rewrite hImage; exact:(bigcup_connected hCommon (fun x hx=>hP x)).
- move=>S [a ha] hOpen hClosed.
  have [O ho hSO]:=hOpen.
  have hSA:S `<=` A by move=>x hx; rewrite hSO in hx; exact hx.1.
  exfalso; apply:hEmpty; exists a; exact:hSA a ha.
Qed.
