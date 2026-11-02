(** Federer (1969), 3.2.26(3), p. 262: the
    Borel partition on which the measurable simple unit
    tangent orientation lies within delta of a fixed
    simple unit vector. Existence uses 3.2.25 and
    separability of the actual finite exterior space. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  cardinality reals constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct EuclideanLinearMaps InnerMetric
  InnerExterior InnerExteriorPositivity ExteriorGrading ExteriorNorm AssociatedSubspace ExteriorIndices FiniteExteriorPowers
  RectifiableSetUP RectifiableOrientationUP RectifiableMeasurableOrientation
  BorelPartialSmallPartition InnerMetricSeparability PartialFunctionUP MeasurableFunctionUP
  HausdorffMeasure HausdorffClosedCoverAgreement MeasureUP MeasureRestriction
  BorelRegularMeasureUP TopologicalBorel.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [rectifiable_orientation_borel_partitions]: the
    partition H and its simple unit centres in the proof
    of 3.2.26(3), p. 262. Its Borel pieces
    cover W except for a Hausdorff-null set and have
    pairwise disjoint actual domains. Every nonempty piece
    selects an actual orientation value on that piece, so
    no density, rank or measurable-frame premise is added. *)
Theorem rectifiable_orientation_borel_partitions (R:realType) m n
    (W:set (R_n R n)) (e:R):
  is_measure_m_rectifiable (@hausdorff_measure R
    (inner_metric_space (@euclidean_inner_productP R n)) m) m W ->
  @borel_set (inner_metric_space (@euclidean_inner_productP R n)) W ->0<e ->
  let E:=inner_metric_space (@exterior_inner_productP R (euclidean_two_nonzero R)
    (R_n R n) (@euclidean_inner_product R n) (@euclidean_inner_productP R n) m) in
  exists (T:partial_function (R_n R n) (exterior_power (R_n R n) m))
      (P:nat->set (R_n R n)) (c:nat->exterior_power (R_n R n) m),
    is_rectifiable_measurable_orientation W T /\
    @is_borel_partial_small_partition R (inner_metric_space (@euclidean_inner_productP R n))
      E W T e P c /\
    (forall i,P i !=set0 ->simple (c i) /\
      exterior_norm (euclidean_two_nonzero R) (@euclidean_inner_productP R n) (c i)= 1) /\
    @hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R n)) m
      (W `\` (\bigcup_i P i))=0%E.
Proof.
move=>hRect hW he E.
pose X:=inner_metric_space (@euclidean_inner_productP R n).
pose H:=@hausdorff_measure R X m.
have hH:=@hausdorff_measure_is_measure R X m.
have hMeas:=borel_regular_borel_measurable hH (@hausdorff_measure_borel_regular R X m) hW.
have [T [hBorel hT]]:=rectifiable_measurable_orientation_borel hRect hMeas.
have hBasis:=@coordinate_e_lambda_basis R (euclidean_two_nonzero R) n m.
have hSeparable:=@finite_inner_metric_separable R (exterior_power (R_n R n) m)
  (@exterior_inner_form R (euclidean_two_nonzero R) (R_n R n)
    (@euclidean_inner_product R n) (@euclidean_inner_productP R n) m)
  (@exterior_inner_productP R (euclidean_two_nonzero R) (R_n R n)
    (@euclidean_inner_product R n) (@euclidean_inner_productP R n) m)
  (Finite.clone (Lambda n m) _) (@coordinate_e_lambda R n m) hBasis.
have [P [c hPartition]]:=@borel_partial_small_partition_exists R X E W T e 0
  hSeparable hW he hBorel.
have hCentres i:P i !=set0 ->simple (c i) /\
    exterior_norm (euclidean_two_nonzero R) (@euclidean_inner_productP R n) (c i)= 1.
  move=>hNonempty; have [x [_ hx]]:=hPartition.2.2.2.1 i hNonempty.
  exact:(rectifiable_orientation_unit_simple hT hx).
have hDomain:=measurable_function_domain (rectifiable_orientation_measurable hT).
have hSet:W `\` (\bigcup_i P i)=W `\` partial_function_domain T.
  rewrite hPartition.2.2.1; apply/seteqP; split.
  - move=>x [hx hn]; split; first exact hx.
    move=>hd; exact:hn (conj hx hd).
  - move=>x [hx hn]; split; first exact hx.
    by move=>[_ hd]; exact:hn hd.
exists T,P,c; split; first exact hT; split; first exact hPartition.
split; first exact hCentres.
rewrite hSet; exact hDomain.
Qed.
