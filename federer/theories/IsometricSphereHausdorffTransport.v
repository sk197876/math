(** Federer (1969), 3.4.12, p. 339, extending the sphere
    comparison in 3.4.8(6),(8), pp. 328–330: an actual
    isometric coordinate chart transports the original unit-sphere
    mass and all exceptional null sets. Apply existing Hausdorff
    isometric embedding and metric-subspace theorems directly. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets functions reals constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerNorm InnerMetric
  MetricSubsetBackground HausdorffMeasure HausdorffMetricSubset HausdorffIsometricEmbedding
  HausdorffUnitSphereMass SphereGammaMass EulerGamma EulerGammaHalfParameters.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section Transport.
Variable R:realType.
Variable X:metricType R.
Variable d:nat.
Local Notation Y:=(inner_metric_space (@euclidean_inner_productP R d)).
Variable S:Y->X.
Variable P:X->Y.
Variable V:set X.
Variable hLeft:cancel S P.
Variable hDistance:forall x y,mdist (S x) (S y)=mdist x y.
Variable hImage:S @` [set y:Y|inner_norm (@euclidean_inner_productP R d) y= 1]=V.
Local Notation M:=([the metricType R of metric_subset V]).

(** Source for [isometric_sphere_hausdorff_mass]: exact original
    finite positive Gamma-normalized sphere mass in an isometric
    coordinate image, supporting 3.4.12, p. 339. *)
Theorem isometric_sphere_hausdorff_mass (hPositive:(0<d)%N):
  @hausdorff_measure R M (d-1) setT=
    (2*(euler_gamma_half R)^+d/euler_gamma (@positive_dimension_half R d hPositive))%:E.
Proof.
rewrite -(@hausdorff_metric_subset_measure R X V (d-1) setT).
have hWhole:(fun u:metric_subset V=>(val u:X)) @` setT=V.
  apply/seteqP;split=>x.
  - move=>[u _ <-];exact:set_valP.
  - move=>hx;exists (exist _ x (mem_set hx));by [].
rewrite hWhole -hImage (@hausdorff_isometric_embedding_invariance R Y X S P hLeft hDistance).
exact:(@hausdorff_unit_sphere_gamma_mass R d hPositive).
Qed.

(** Source for [isometric_sphere_coordinate_null]: actual coordinate
    exceptional null sets remain null in the original sphere,
    without a measurability premise, 3.4.12, p. 339. *)
Theorem isometric_sphere_coordinate_null (D:set Y):
  @hausdorff_measure R Y (d-1) [set y|inner_norm (@euclidean_inner_productP R d) y= 1 /\D y]=0%:E ->
  @hausdorff_measure R M (d-1) [set u|D (P (val u))]=0%:E.
Proof.
move=>hNull.
rewrite -(@hausdorff_metric_subset_measure R X V (d-1) [set u|D (P (val u))]).
have hSame:(fun u:metric_subset V=>(val u:X)) @` [set u|D (P (val u))]=
  S @` [set y:Y|inner_norm (@euclidean_inner_productP R d) y= 1 /\D y].
  apply/seteqP;split=>x.
  - move=>[u hD <-].
    have hu:V (val u):=set_valP u.
    have huImage:(S @` [set y:Y|inner_norm (@euclidean_inner_productP R d) y= 1]) (val u).
      by rewrite hImage.
    have [y hy hY]:=huImage.
    exists y;last exact:hY.
    split;first exact:hy.
    have hP:P (val u)=y by rewrite -hY hLeft.
    by rewrite -hP.
  - move=>[y [hy hD] <-].
    have hV:V (S y) by rewrite -hImage;exists y.
    exists (exist _ (S y) (mem_set hV));last by [].
    change (D (P (S y)));by rewrite hLeft.
rewrite hSame (@hausdorff_isometric_embedding_invariance R Y X S P hLeft hDistance).
exact:hNull.
Qed.
End Transport.
