(** Federer (1969), 4.1.11, p. 365: a second scalar
    cutoff gives an actual compact replacement of the first
    projection pullback near the original product support.
    This supports the two zero-degree endpoint terms. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormDifferentialUP NormDifferentialLinear
  NormFiniteLinearBound NormRegularity NormRegularityOperations
  InnerNorm HilbertFormCompactness GrassmannAbbreviations FiniteCoordinates
  EuclideanInnerProduct EuclideanBlockLinearMaps EuclideanCartesianMap
  CurrentCartesianDomain CurrentCartesianProjections AlternatingZero CurrentSpaces CurrentCartesianProductSealed
  CurrentCartesianTestProductSealed CurrentCartesianFirstCutoffValues CurrentDegreeTransport
  CurrentCartesianOpenCylinders CurrentCartesianSupportUpper CurrentPushforwardUP
  SmoothTestSpaces SmoothFormPullbackSealed NormMetric NormOpenTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Section CurrentCartesianFirstCutoffReplacement.
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
Local Notation Image := (fun z (hz:AB z)=>hz.1).
Local Notation hSmooth := (@current_cartesian_first_projection_smooth R m n A B hA hB).
Local Notation Tr := (fun a b (e:a=b)=>@current_test_degree_transport R h2 (m+n) AB hAB a b e).
Local Open Scope classical_set_scope.

(** Source for [current_cartesian_first_cutoff_replacement]:
    a second-factor scalar cutoff equal to one near spt T
    supplies an actual compact replacement of the original
    first-projection pullback near spt(S times T), supporting
    Federer 4.1.11, p. 365. *)
Theorem current_cartesian_first_cutoff_replacement
    (gamma:@current_test_space R h2 n B hB 0%N) (W:set Y):
  @open (real_norm_metric_space hNY) W->
  (@current_support R h2 n B hB j T `<=` W)->
  (forall y,W y->@current_test_value R h2 n B hB 0%N gamma y=@zero_form R Y R^o 1)->
  forall alpha:@current_test_space R h2 m A hA (i+j),
    @is_current_pullback_test_replacement R h2 (m+n) m (i+j) AB A hAB hA Product
      p Image hSmooth alpha (Tr _ _ (addn0 (i+j)) (Pure (i+j) 0 alpha gamma)).
Proof.
move=>hW hTW hGamma alpha.
exists (AB `&` [set z|W (q z)]);split.
- exact:(@current_cartesian_second_cylinder_open R m n A B hA hB W hW).
- split.
  + move=>z hz;split;first exact:hz.1.
    have hFactors:=@current_cartesian_support_upper R h2 m n i j A B hA hB S T z hz.
    exact:(hTW (q z) hFactors.2).
  + split;first by move=>z hz;exact:hz.1.
    move=>z [hz hWz].
    exact:(@current_cartesian_first_cutoff_values R h2 m n A B hA hB (i+j)
      alpha gamma z hz (@hGamma (q z) hWz)).
Qed.
End CurrentCartesianFirstCutoffReplacement.
