(** Federer (1969), 4.1.8, p. 360: the Cartesian projections
    p and q are smooth and have their original constant differentials.
    All maps are the existing block projections of 2.6.5, p. 120.
    The earlier finite-dimensional linear bound and linear calculus
    prove these supporting laws, including empty coordinate blocks. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormDifferentialUP NormDifferentialLinear
  NormFiniteLinearBound NormRegularity NormRegularityOperations
  InnerNorm HilbertFormCompactness GrassmannAbbreviations FiniteCoordinates
  EuclideanInnerProduct EuclideanBlockLinearMaps EuclideanCartesianMap
  CurrentCartesianDomain CurrentCartesianProjections AlternatingZero CurrentSpaces CurrentCartesianProductSealed
  CurrentCartesianTestProductSealed CurrentCartesianProjectionCutoffValues CurrentDegreeTransport
  CurrentCartesianOpenCylinders CurrentCartesianSupportUpper CurrentPushforwardUP
  SmoothTestSpaces SmoothFormPullbackSealed NormMetric NormOpenTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Section CurrentCartesianProjectionCutoffReplacement.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables m n:nat.
Local Notation X := (R_n R m).
Local Notation Y := (R_n R n).
Local Notation Z := (R_n R (m+n)).
Local Notation NX := (inner_norm (@euclidean_inner_productP R m)).
Local Notation NY := (inner_norm (@euclidean_inner_productP R n)).
Local Notation NZ := (inner_norm (@euclidean_inner_productP R (m+n))).
Local Notation hNX := (inner_norm_real_norm (@euclidean_inner_productP R m)).
Local Notation hNY := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation hNZ := (inner_norm_real_norm (@euclidean_inner_productP R (m+n))).
Local Notation p := (@euclidean_first_block_map R m n).
Local Notation q := (@euclidean_last_block_map R m n).
Variable A:set X.
Variable B:set Y.
Hypothesis hA:forall a,A a->norm_domain_interior NX A a.
Hypothesis hB:forall b,B b->norm_domain_interior NY B b.
Local Notation AB := (@euclidean_cartesian_set R m n A B).
Local Notation hAB := (@current_cartesian_domain_open R m n A B hA hB).

Variables i j:nat.
Variable S:@current_space R h2 m A hA i.
Variable T:@current_space R h2 n B hB j.
Local Notation Product := (@CartesianCurrentProduct.value R h2 m n i j A B hA hB S T).
Local Notation Pure := (fun k l=>@CartesianTestProduct.value R h2 m n A B hA hB k l).
Local Notation Image := (fun z (hz:AB z)=>hz.2).
Local Notation hSmooth := (@current_cartesian_last_projection_smooth R m n A B hA hB).
Local Notation Tr := (fun a b (e:a=b)=>@current_test_degree_transport R h2 (m+n) AB hAB a b e).
Local Open Scope classical_set_scope.

(** Source for [current_cartesian_projection_cutoff_replacement]:
    a first-factor scalar cutoff equal to one near
    spt S supplies an actual compact replacement of
    the original q pullback near spt(S times T),
    supporting both projection formulas in Federer 4.1.8,
    p. 361. No compactness premise on T is added. *)
Theorem current_cartesian_projection_cutoff_replacement
    (gamma:@current_test_space R h2 m A hA 0%N) (W:set X):
  @open (real_norm_metric_space hNX) W->
  (@current_support R h2 m A hA i S `<=` W)->
  (forall x,W x->@current_test_value R h2 m A hA 0%N gamma x=@zero_form R X R^o 1)->
  forall beta:@current_test_space R h2 n B hB (i+j),
    @is_current_pullback_test_replacement R h2 (m+n) n (i+j) AB B hAB hB Product
      q Image hSmooth beta (Tr _ _ (add0n (i+j)) (Pure 0 (i+j) gamma beta)).
Proof.
move=>hW hSW hGamma beta.
exists (AB `&` [set z|W (p z)]);split.
- exact:(@current_cartesian_first_cylinder_open R m n A B hA hB W hW).
- split.
  + move=>z hz;split;first exact:hz.1.
    have hFactors:=@current_cartesian_support_upper R h2 m n i j A B hA hB S T z hz.
    exact:(hSW (p z) hFactors.1).
  + split;first by move=>z hz;exact:hz.1.
    move=>z [hz hWz].
    exact:(@current_cartesian_projection_cutoff_values R h2 m n A B hA hB (i+j)
      gamma beta z hz (@hGamma (p z) hWz)).
Qed.
End CurrentCartesianProjectionCutoffReplacement.
