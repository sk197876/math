(** Federer (1969), 4.1.23, p. 379:
    the density current of the selected disjoint
    rectangular union is the literal finite sum
    of its original cell currents. Pointwise
    characteristic identities precede the integral identity. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  functions classical_sets reals constructive_ereal topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP
  NormOpenDomainLaws InnerNorm HilbertFormCompactness GrassmannAbbreviations
  EuclideanInnerProduct ExteriorGrading CurrentSpaces CurrentCharacteristicDensity
  CurrentDensityAction CurrentDensityArithmetic CurrentDensityUniqueness
  EuclideanLebesgueDimensions EuclideanDistributionMeasureContext
  CharacteristicFunctionUP CharacteristicFunctionSealed MeasureUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [finite_disjoint_characteristic_sum]:
    1_(union A_i)=sum_i 1_Ai,
    the exact pointwise identity used
    for rectangular step fields in
    Federer 4.1.23, p. 379.
    Empty cells, empty families and
    points on their boundaries are included. *)
Lemma finite_disjoint_characteristic_sum (R : realType) (X : choiceType)
    (I : finType) (A : I -> set X)
    (hDisjoint : forall i j, i!=j -> forall x, A i x -> A j x -> False) x :
  @CharacteristicFunction.value R X (\bigcup_i A i) x=
    \sum_i @CharacteristicFunction.value R X (A i) x.
Proof.
pose H := \bigcup_i A i.
pose hH := @CharacteristicFunction.laws R X H.
pose hA := fun i => @CharacteristicFunction.laws R X (A i).
case: (pselect (H x))=> hx.
- have [i _ hi] := hx.
  rewrite (characteristic_on_set hH hx) (bigD1 i) //
    (characteristic_on_set (hA i) hi).
  have hOther : \sum_(j | j!=i) @CharacteristicFunction.value R X (A j) x=0.
    apply: big1=> j hJI.
    apply: (@characteristic_off_set R X (A j)
      (@CharacteristicFunction.value R X (A j)) (hA j) x)=> hj.
    exact: (@hDisjoint j i hJI x hj hi).
  change (1 = 1 + \sum_(j | j!=i) @CharacteristicFunction.value R X (A j) x).
  by rewrite hOther addr0.
- rewrite (characteristic_off_set hH hx); symmetry.
  apply: big1=> i _.
  apply: (@characteristic_off_set R X (A i)
    (@CharacteristicFunction.value R X (A i)) (hA i) x)=> hi.
  apply: hx; by exists i.
Qed.

(** Source for [characteristic_current_disjoint_finite_union]:
    the actual current on the
    finite disjoint rectangular union is
    the sum of its actual
    cell currents, supporting Federer
    4.1.23, p. 379.
    No closedness, finite mass or
    choice of representation is needed. *)
Theorem characteristic_current_disjoint_finite_union (R : realType)
    (h2 : (1+1:R)!=0) n m (I : finType) (A : I -> set (R_n R n))
    (hA : forall i, measure_measurable (@euclidean_lebesgue_measure R n) (A i))
    (hH : measure_measurable (@euclidean_lebesgue_measure R n) (\bigcup_i A i))
    (hDisjoint : forall i j, i!=j -> forall x, A i x -> A j x -> False)
    (z : exterior_power (R_n R n) m) :
  let cell := fun B hB => @current_characteristic_density R h2 n m
    (@euclidean_lebesgue_measure R n) (euclidean_lebesgue_is_measure R n)
    (@euclidean_distribution_measure_borel R n)
    (@euclidean_distribution_measure_compact_finite R n) B hB z in
  cell (\bigcup_i A i) hH=\sum_i cell (A i) (hA i).
Proof.
move=> cell.
have hUnion := @current_characteristic_density_action R h2 n m
  (@euclidean_lebesgue_measure R n) (euclidean_lebesgue_is_measure R n)
  (@euclidean_distribution_measure_borel R n)
  (@euclidean_distribution_measure_compact_finite R n) (\bigcup_i A i) hH z.
have hSum := @current_density_finite_sum_action R h2 n m
  (@euclidean_lebesgue_measure R n) (euclidean_lebesgue_is_measure R n) I
  (fun i x => @CharacteristicFunction.value R (R_n R n) (A i) x*:z)
  (fun i => cell (A i) (hA i))
  (fun i => @current_characteristic_density_action R h2 n m
    (@euclidean_lebesgue_measure R n) (euclidean_lebesgue_is_measure R n)
    (@euclidean_distribution_measure_borel R n)
    (@euclidean_distribution_measure_compact_finite R n) (A i) (hA i) z).
have hField : (fun x => @CharacteristicFunction.value R (R_n R n) (\bigcup_i A i) x*:z)=
    (fun x => \sum_i @CharacteristicFunction.value R (R_n R n) (A i) x*:z).
  apply: funext=> x; by rewrite
    (@finite_disjoint_characteristic_sum R (R_n R n) I A hDisjoint x) scaler_suml.
rewrite hField in hUnion.
exact: (@current_density_action_unique R h2 n m (@euclidean_lebesgue_measure R n)
  _ _ _ hUnion hSum).
Qed.
