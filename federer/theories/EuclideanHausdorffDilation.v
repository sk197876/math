(** Federer (1969), 3.2.13, p. 250: dilation
    of the radius-r sphere contributes r^(m-1).
    The actual Hausdorff image measure scales in
    every natural degree, by the two Lipschitz
    bounds of 2.10.11. Infinite masses are retained. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerNorm InnerNormInequalities InnerMetric
  LipschitzUP HausdorffMeasure HausdorffLipschitzImages MeasureUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [euclidean_positive_dilation_lipschitz]: distance
    scaling by a positive r in the
    polar sphere change of variables, Federer
    3.2.13, p. 250. The origin and
    degree-zero boundaries are not excluded. *)
Lemma euclidean_positive_dilation_lipschitz (R:realType) m (r:R):
  (0<r)%R ->is_metric_lipschitz_bound setT
    (fun x:inner_metric_space (@euclidean_inner_productP R m)=>r*:x) r.
Proof.
move=>hr; split; first exact:ltW hr.
move=>x y _ _; rewrite !inner_metric_distanceE -scalerBr inner_normZ (gtr0_norm hr); exact:lexx.
Qed.

(** Source for [euclidean_hausdorff_positive_dilation]: the
    r^(m-1) factor in the second polar
    identity of Federer 3.2.13, p. 250,
    proved in every natural Hausdorff degree.
    Both inequalities use 2.10.11; no finiteness,
    measurability or positive-degree premise is added. *)
Lemma euclidean_hausdorff_positive_dilation (R:realType) m k (r:R)
    (A:set (inner_metric_space (@euclidean_inner_productP R m))):
  (0<r)%R ->
  @hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R m)) k
    ((fun x=>r*:x) @` A)=
  (r^+k)%R%:E* @hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R m)) k A.
Proof.
move=>hr.
pose X:=inner_metric_space (@euclidean_inner_productP R m).
pose H:=@hausdorff_measure R X k.
have hNe:(r!= 0)%R:=lt0r_neq0 hr.
have hInv:(0<r^-1)%R by rewrite invr_gt0.
have hForward:=@hausdorff_positive_lipschitz_image_bound R X X
  (fun x:X=>r*:x) r k hr (@euclidean_positive_dilation_lipschitz R m r hr) A.
have hBackward:=@hausdorff_positive_lipschitz_image_bound R X X
  (fun x:X=>r^-1*:x) r^-1 k hInv (@euclidean_positive_dilation_lipschitz R m r^-1 hInv)
  ((fun x:X=>r*:x) @` A).
have hImage:(fun x:X=>r^-1*:x) @` ((fun x:X=>r*:x) @` A)=A.
  apply/seteqP; split=>x.
  - move=>[y [z hz <-] <-]; by rewrite scalerA mulVf // scale1r.
  - move=>hx; exists (r*:x).
    + by exists x.
    + by rewrite scalerA mulVf // scale1r.
rewrite hImage in hBackward.
have hPower:(0<r^+k)%R:=exprn_gt0 k hr.
have hScale:0<=(r^+k)%R%:E by rewrite lee_fin; exact:ltW hPower.
have hLower:=lee_wpmul2l hScale hBackward.
rewrite muleA -EFinM -exprMn mulfV // expr1n mul1e in hLower.
apply/eqP; rewrite eq_le hForward hLower; by [].
Qed.
