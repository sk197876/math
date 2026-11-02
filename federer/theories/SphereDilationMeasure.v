(** Federer (1969), 3.2.13, p. 250: the
    radius-r sphere measure is r^(m-1)
    times the image of the unit-sphere measure.
    The identity is proved for actual restricted
    Hausdorff measures and all sets, including infinite mass. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerNorm InnerNormInequalities InnerMetric
  EuclideanHausdorffDilation HausdorffMeasure MeasureRestriction MeasurePushforward MeasureScaleIntegral.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [spherical_hausdorff_measure]: the restriction
    of H^(m-1) to a radius-r sphere
    in Federer 3.2.13, p. 250,
    expressed in any natural Hausdorff degree by
    the existing restriction operation of 2.1.2, p. 54. *)
Definition spherical_hausdorff_measure (R:realType) (m k:nat) (r:R):=
  measure_restrict (@hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R m)) k)
    [set x|inner_norm (@euclidean_inner_productP R m) x=r].
Arguments spherical_hausdorff_measure {R} m k r A.

(** Source for [sphere_dilation_cutset]: exact set
    change of variables between positive-radius and
    unit spheres, supporting the second polar
    identity in Federer 3.2.13, p. 250. *)
Lemma sphere_dilation_cutset (R:realType) m (r:R)
    (B:set (inner_metric_space (@euclidean_inner_productP R m))):
  (0<r)%R ->
  (fun x=>r*:x) @` ([set x|inner_norm (@euclidean_inner_productP R m) x= 1%R] `&`
    ((fun x=>r*:x) @^-1` B))=
    [set x|inner_norm (@euclidean_inner_productP R m) x=r] `&` B.
Proof.
move=>hr.
have hNe:(r!= 0)%R:=lt0r_neq0 hr.
have hInv:(0<r^-1)%R by rewrite invr_gt0.
apply/seteqP; split=>y /=.
- move=>[x [hx hB] <-]; split=>//.
  by rewrite inner_normZ (gtr0_norm hr) hx mulr1.
- move=>[hy hB].
  have hCancel:r*:(r^-1*:y)=y by rewrite scalerA mulfV // scale1r.
  exists (r^-1*:y); last exact hCancel.
  split.
  + by rewrite inner_normZ (gtr0_norm hInv) hy mulVf.
  + by rewrite hCancel.
Qed.

(** Source for [spherical_hausdorff_dilation_pushforward]: the
    r^(m-1) sphere scaling used in the
    second polar equality of Federer 3.2.13,
    p. 250. The supporting law is proved
    for every natural degree, without assuming sphere
    finiteness, target measurability or positive source dimension. *)
Lemma spherical_hausdorff_dilation_pushforward (R:realType) m k (r:R):
  (0<r)%R ->spherical_hausdorff_measure m k r=
    measure_scale (r^+k)%R (measure_pushforward
      (fun x:inner_metric_space (@euclidean_inner_productP R m)=>r*:x)
      (spherical_hausdorff_measure m k (1%R:R))).
Proof.
move=>hr; apply:funext=>B.
rewrite /spherical_hausdorff_measure /measure_scale /measure_pushforward /measure_restrict.
rewrite -(sphere_dilation_cutset B hr).
exact (@euclidean_hausdorff_positive_dilation R m k r _ hr).
Qed.
