(** Federer (1969), 4.1.8, p. 362: the
    original scalar segment factor is the original
    coordinate-oriented interval current. Retain its actual
    full containing domain and the proved signed integral. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets
  reals constructive_ereal topology normedtype.
From Federer Require Import RealNormUP NormDifferentialUP NormOpenDomainLaws InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct EuclideanOneCoordinate CurrentSpaces
  OrientedSegmentFactor ScalarSegmentFactors OrientedSegmentCurrentSealed ScalarOrientedSegmentInterval
  EuclideanCharacteristicCurrent OpenEuclideanCharacteristicCurrent OpenEuclideanCharacteristicFull
  EuclideanLebesgueDimensions RealMetricBackground MeasureUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import numFieldTopology.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [scalar_segment_factor_interval]: the actual
    [u,v] factor equals the actual Euclidean
    characteristic current of u<x<v when u<v,
    supporting the finite product identity of Federer
    4.1.8, p. 362. *)
Lemma scalar_segment_factor_interval (R:realType) (h2:(1+1:R)!=0) (a:R*R)
    (hB:measure_measurable (@euclidean_lebesgue_measure R 1%N)
      [set x:R_n R 1%N|a.1<x ord0<a.2]):
  a.1<a.2->@oriented_segment_factor_current R h2 (@scalar_segment_factor R a)=
    @open_euclidean_characteristic_current R h2 1%N (fun _=>True)
      (fun x (_:True)=>@norm_full_domain_interior R (R_n R 1%N)
        (inner_norm (@euclidean_inner_productP R 1%N)) x)
      [set x:R_n R 1%N|a.1<x ord0<a.2] hB.
Proof.
move=>ha.
have hSet:[set x:R_n R 1%N|a.1<x ord0<a.2]=
    (@euclidean_one_project R @^-1` (`]a.1,a.2[:set (real_line_metric R))).
  apply:funext=>x;apply:propext.
  change (is_true (a.1<x ord0<a.2) <-> is_true (x ord0 \in `]a.1,a.2[%R)).
  by rewrite in_itv /=.
have hEqual:=@open_euclidean_characteristic_set_equal R h2 1%N (fun _=>True)
  (fun x (_:True)=>@norm_full_domain_interior R (R_n R 1%N)
    (inner_norm (@euclidean_inner_productP R 1%N)) x)
  [set x:R_n R 1%N|a.1<x ord0<a.2]
  (@euclidean_one_project R @^-1` (`]a.1,a.2[:set (real_line_metric R)))
  hB (@scalar_segment_interval_measurable R a.1 a.2) hSet.
rewrite hEqual open_euclidean_characteristic_current_full.
exact:(@scalar_oriented_segment_interval_current R h2 a.1 a.2 ha).
Qed.
