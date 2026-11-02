(** Federer (1969), 3.2.36, p. 273: actual metric
    isometric maps preserve the affine segment parameter. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets topology.
From Federer Require Import RealMetricBackground InnerProductUP InnerMetric InnerConvex Bilinear
  MetricIsometricInjectionAffine.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [metric_isometric_segment_identity]: the segment identity
    needed for closed convex preimage covers in the Q_1 assertion
    of Federer 3.2.36, p. 273. The actual affine classification
    proves the equality for every real segment parameter, without
    preassigned affine structure, surjectivity or dimension hypotheses. *)
Lemma metric_isometric_segment_identity (R:realType) (V W:lmodType R)
    (B:V->V->R) (C:W->W->R) (hB:is_inner_product B) (hC:is_inner_product C) (f:V->W):
  (forall x y,@mdist R (inner_metric_space hC) (f x) (f y)=
    @mdist R (inner_metric_space hB) x y) ->
  forall x y t,f ((1-t)*:x+t*:y)=(1-t)*:f x+t*:f y.
Proof.
move=>hMetric x y t.
have [hLinear _]:=@metric_isometric_injection_linear_part R V W B C hB hC f hMetric.
pose g:=fun x:V=>f x-f 0.
have hGLinear:linear g:=hLinear.
have hValue u:f u=f 0+g u by rewrite /g addrC subrK.
have hSum:g ((1-t)*:x+t*:y)=(1-t)*:g x+t*:g y.
  by rewrite (linD hGLinear) !(linZ hGLinear).
have hAlgebra (a b c:W) (s:R):c+((1-s)*:a+s*:b)=(1-s)*:(c+a)+s*:(c+b).
  by rewrite !scalerDr addrACA -scalerDl subrK scale1r.
by rewrite (hValue ((1-t)*:x+t*:y)) hSum hAlgebra -(hValue x) -(hValue y).
Qed.

(** Source for [metric_isometric_convex_preimage]: original preimages
    of convex target generators are convex in the reverse cover
    transport of Federer 3.2.36, p. 273. The actual segment
    identity discharges affine preservation; no nonemptiness, closedness
    or measurability assumption on the target generator is needed. *)
Lemma metric_isometric_convex_preimage (R:realType) (V W:lmodType R)
    (B:V->V->R) (C:W->W->R) (hB:is_inner_product B) (hC:is_inner_product C)
    (f:V->W) (A:set W):
  (forall x y,@mdist R (inner_metric_space hC) (f x) (f y)=
    @mdist R (inner_metric_space hB) x y) ->is_inner_convex A ->
  is_inner_convex (f @^-1` A).
Proof.
move=>hMetric hA x y hx hy t ht0 ht1.
change (A (f ((1-t)*:x+t*:y))).
rewrite (@metric_isometric_segment_identity R V W B C hB hC f hMetric).
exact:hA _ _ hx hy t ht0 ht1.
Qed.
