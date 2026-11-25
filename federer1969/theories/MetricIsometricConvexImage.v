(** Federer (1969), 3.2.36, p. 273: convexity is
    preserved by the actual arbitrary metric isometric injection. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets topology.
From Federer Require Import RealMetricBackground InnerProductUP InnerMetric InnerConvex Bilinear
  MetricIsometricInjectionAffine.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [metric_isometric_convex_image]: the convex image
    used in the isometric-injection assertions of Federer 3.2.36,
    p. 273. The proved affine classification gives the exact segment
    identity for the original f. Consequently every original convex
    source has a convex image, without a compactness, closedness,
    measurability or preassigned affine-map hypothesis. *)
Lemma metric_isometric_convex_image (R:realType) (V W:lmodType R)
    (B:V->V->R) (C:W->W->R) (hB:is_inner_product B) (hC:is_inner_product C)
    (f:V->W) (A:set V):
  (forall x y,@mdist R (inner_metric_space hC) (f x) (f y)=
    @mdist R (inner_metric_space hB) x y) ->
  is_inner_convex A ->is_inner_convex (f @` A).
Proof.
move=>hMetric hA.
have [hLinear _]:=@metric_isometric_injection_linear_part R V W B C hB hC f hMetric.
pose g:=fun x:V=>f x-f 0.
have hGLinear:linear g:=hLinear.
have hValue x:f x=f 0+g x by rewrite /g addrC subrK.
move=>u v [x hx <-] [y hy <-] t ht0 ht1.
exists ((1-t)*:x+t*:y); first exact:hA x y hx hy t ht0 ht1.
have hGSum:g ((1-t)*:x+t*:y)=(1-t)*:g x+t*:g y.
  by rewrite (linD hGLinear) !(linZ hGLinear).
rewrite (hValue ((1-t)*:x+t*:y)) hGSum.
have hAlgebra (a b c:W) (s:R):
    c+((1-s)*:a+s*:b)=(1-s)*:(c+a)+s*:(c+b).
  by rewrite !scalerDr addrACA -scalerDl subrK scale1r.
by rewrite hAlgebra -(hValue x) -(hValue y).
Qed.
