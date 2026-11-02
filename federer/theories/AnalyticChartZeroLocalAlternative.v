(** Federer (1969), 3.2.33, p. 270: analytic
    rank equations on each connected coordinate domain are
    either identically zero or Hausdorff null. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets
  constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerNorm InnerMetric
  HilbertFormCompactness RealNormUP InnerNormConnectedAdapter InnerNormTopologyAdapters NormConvexConnected
  NormCoordinateSystemUP NormRegularity NormClassZeroTopology EuclideanAnalyticRoots
  EuclideanLebesgueDimensions HausdorffMeasure MeasureUP MeasureAlmostBasic
  ClassOneDomainNullImage AnalyticChartZeroLocusUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [analytic_chart_zero_locus_local_alternative]:
    the local root-set inference behind S in Federer
    3.2.33, p. 270. The corrected reference is
    3.1.24 (erratum p. 5, book p. 270 line 25).
    Convex coordinates give connectedness; actual local
    class-one bounds transport null root sets to W. *)
Theorem analytic_chart_zero_locus_local_alternative (R:realType) n m
    (W P:set (R_n R n)) a:
  @is_analytic_chart_zero_locus R n m W P ->W a ->
  exists T:set (inner_metric_space (@euclidean_inner_productP R n)),
    open T /\T a /\
    (W `&` T `<=` P \/
      @hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R n)) m (P `&` T)=0%E).
Proof.
move=>hP ha.
have [T [V [phi [psi [h [haT [hConvex [hc [hAnalytic hEquation]]]]]]]]]:=
  analytic_chart_zero_locus_coordinates hP ha.
have hConnected:= (inner_norm_connectedP (@euclidean_inner_productP R m) V).2
  (@norm_inner_convex_connected R (R_n R m) (inner_norm (@euclidean_inner_productP R m))
    (inner_norm_real_norm (@euclidean_inner_productP R m)) V hConvex).
have hRoots:=@euclidean_analytic_roots R m R^o (fun t:R^o=>`|t|)
  (@scalar_absolute_value_norm R) V h hConnected hAnalytic.
exists T; split.
- apply:(inner_norm_openP (@euclidean_inner_productP R n) T).2.
  exact:norm_class_zero_domain_open (norm_class_continuous (norm_coordinate_class_forward hc)).
- split; first exact haT.
  case:hRoots=>[hAll|hNull].
  + left=>x [hx ht]; apply:(hEquation x hx ht).2.
    have hv:=norm_coordinate_forward_range hc ht; rewrite -hAll in hv; exact hv.2.
  + right.
    have hImageNull:=@class_one_domain_null_image R m n V
      (fun u=>V u /\h u= 0) psi
      ((norm_class_firstP (inner_norm_real_norm (@euclidean_inner_productP R m))
        (inner_norm_real_norm (@euclidean_inner_productP R n)) V psi).1
        (norm_coordinate_class_backward hc)) (fun u hu=>hu.1) hNull.
    apply:(measure_null_subset (@hausdorff_measure_is_measure R
      (inner_metric_space (@euclidean_inner_productP R n)) m) _ hImageNull).
    move=>x [hx ht].
    have hxW:=analytic_chart_zero_locus_subset hP hx.
    exists (phi x).
    * split; first exact:(@norm_coordinate_forward_range R (R_n R n) (R_n R m)
        (inner_norm (@euclidean_inner_productP R n)) (inner_norm (@euclidean_inner_productP R m))
        (inner_norm_real_norm (@euclidean_inner_productP R n))
        (inner_norm_real_norm (@euclidean_inner_productP R m)) W T V phi psi 1%N hc x ht).
      exact:(hEquation x hxW ht).1 hx.
    * exact:(@norm_coordinate_base_inverse R (R_n R n) (R_n R m)
        (inner_norm (@euclidean_inner_productP R n)) (inner_norm (@euclidean_inner_productP R m))
        (inner_norm_real_norm (@euclidean_inner_productP R n))
        (inner_norm_real_norm (@euclidean_inner_productP R m)) W T V phi psi 1%N hc x hxW ht).
Qed.
