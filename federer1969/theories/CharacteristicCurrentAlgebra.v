(** Federer (1969), 4.1.23, p. 379:
    the actual constant-vector cell currents respect
    equal measurable sets and finite vector operations.
    Reuse the original density action and its
    uniqueness, without choosing quotient representatives. *)
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

Section CharacteristicCurrentAlgebra.
Variable R : realType.
Hypothesis h2 : (1+1:R)!=0.
Variables n m : nat.
Local Notation X := (R_n R n).
Local Notation V := (exterior_power X m).
Local Notation Leb := (@euclidean_lebesgue_measure R n).
Local Notation hLeb := (euclidean_lebesgue_is_measure R n).
Local Notation cell := (fun A hA z => @current_characteristic_density R h2 n m
  Leb hLeb (@euclidean_distribution_measure_borel R n)
  (@euclidean_distribution_measure_compact_finite R n) A hA z).

(** Source for [characteristic_current_set_congruence]:
    equal original measurable cells give
    the same actual density current,
    supporting the rectangle identifications in
    Federer 4.1.23, pp. 379–380.
    Different measurability witnesses need not
    be supplied as equal by callers. *)
Lemma characteristic_current_set_congruence (A B : set X)
    (hA : measure_measurable Leb A) (hB : measure_measurable Leb B) (z : V) :
  A=B -> cell A hA z=cell B hB z.
Proof.
move=> hEqual; subst B.
have hProof : hB=hA := Prop_irrelevance _ _.
by subst hB.
Qed.

(** Source for [characteristic_current_coefficient_zero]:
    a zero coefficient gives the
    actual zero cell current in
    Federer 4.1.23, p. 379,
    including on nonempty measurable cells. *)
Lemma characteristic_current_coefficient_zero (A : set X)
    (hA : measure_measurable Leb A) : cell A hA 0=0.
Proof.
have hAction := @current_characteristic_density_action R h2 n m Leb hLeb
  (@euclidean_distribution_measure_borel R n)
  (@euclidean_distribution_measure_compact_finite R n) A hA (0:V).
have hField : (fun x : X => @CharacteristicFunction.value R X A x*:(0:V))=
    (fun _ : X => (0:V)).
  by apply: funext=> x; rewrite scaler0.
rewrite hField in hAction.
exact: (@current_density_action_unique R h2 n m Leb _ _ _ hAction
  (@current_density_zero_action R h2 n m Leb hLeb)).
Qed.

(** Source for [characteristic_current_coefficient_scale]:
    signed real scaling of a
    cell coefficient is the same
    scaling of its actual current,
    used in the simple-unit and
    scalar-sign reductions of Federer
    4.1.23, p. 379. *)
Lemma characteristic_current_coefficient_scale (A : set X)
    (hA : measure_measurable Leb A) c (z : V) :
  cell A hA (c*:z)=c*:cell A hA z.
Proof.
have hCell := @current_characteristic_density_action R h2 n m Leb hLeb
  (@euclidean_distribution_measure_borel R n)
  (@euclidean_distribution_measure_compact_finite R n) A hA (c*:z).
have hScaled := @current_density_scaled_action R h2 n m Leb hLeb
  (fun x => @CharacteristicFunction.value R X A x*:z) (cell A hA z) c
  (@current_characteristic_density_action R h2 n m Leb hLeb
    (@euclidean_distribution_measure_borel R n)
    (@euclidean_distribution_measure_compact_finite R n) A hA z).
have hField : (fun x : X => @CharacteristicFunction.value R X A x*:(c*:z))=
    (fun x => c*:(@CharacteristicFunction.value R X A x*:z)).
  apply: funext=> x; by rewrite !scalerA mulrC.
rewrite hField in hCell.
exact: (@current_density_action_unique R h2 n m Leb _ _ _ hCell hScaled).
Qed.

(** Source for [characteristic_current_coefficient_finite_sum]:
    the original attained simple decomposition
    of a cell coefficient gives
    the literal finite sum of
    actual cell currents, supporting
    Federer 4.1.23, p. 379. *)
Lemma characteristic_current_coefficient_finite_sum (A : set X)
    (hA : measure_measurable Leb A) (I : finType) (z : I -> V) :
  cell A hA (\sum_i z i)=\sum_i cell A hA (z i).
Proof.
have hCell := @current_characteristic_density_action R h2 n m Leb hLeb
  (@euclidean_distribution_measure_borel R n)
  (@euclidean_distribution_measure_compact_finite R n) A hA (\sum_i z i).
have hSum := @current_density_finite_sum_action R h2 n m Leb hLeb I
  (fun i x => @CharacteristicFunction.value R X A x*:z i)
  (fun i => cell A hA (z i))
  (fun i => @current_characteristic_density_action R h2 n m Leb hLeb
    (@euclidean_distribution_measure_borel R n)
    (@euclidean_distribution_measure_compact_finite R n) A hA (z i)).
have hField : (fun x : X => @CharacteristicFunction.value R X A x*:(\sum_i z i))=
    (fun x => \sum_i @CharacteristicFunction.value R X A x*:z i).
  by apply: funext=> x; rewrite scaler_sumr.
rewrite hField in hCell.
exact: (@current_density_action_unique R h2 n m Leb _ _ _ hCell hSum).
Qed.
End CharacteristicCurrentAlgebra.
