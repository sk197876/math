(** Federer (1969), 4.1.23, p. 379:
    signed scaling preserves the completed unit-cell
    approximation with its original mass cost.
    The coefficient zero is handled first;
    other signs use the actual absolute scalar
    factor in both original norms. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  functions classical_sets reals constructive_ereal topology.
From Federer Require Import Hom ModuleQuotient RealNormUP NormMetric NormDifferentialUP
  NormOpenDomainLaws InnerNorm HilbertFormCompactness GrassmannAbbreviations
  EuclideanInnerProduct ExteriorGrading CurrentSpaces CurrentCoefficientNorms
  CurrentCharacteristicDensity CurrentMassSealed CurrentMassFiniteAlgebra
  CurrentFiniteMassLinearBound CurrentFlatNorm CurrentFlatFiniteArithmetic
  SmoothCompactSet PolyhedralCurrentAlgebra CompactCharacteristicCurrent
  CharacteristicCurrentAlgebra EuclideanLebesgueDimensions
  EuclideanDistributionMeasureContext MeasureUP MeasureBasic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section ScaledCellApproximation.
Variable R : realType.
Hypothesis h2 : (1+1:R)!=0.
Variables n m : nat.
Local Notation X := (R_n R n).
Local Notation hNX := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation Full := (fun _ : X => True).
Local Notation hFull := (fun (x : X) (_ : True) => norm_full_domain_interior
  (inner_norm (@euclidean_inner_productP R n)) x).
Local Notation Current := (@current_space R h2 n Full hFull m).
Local Notation V := (exterior_power X m).
Local Notation VN := (@current_vector_mass R h2 n m).
Local Notation hVN := (@current_vector_mass_real_norm R h2 n m).
Local Notation M := (@CurrentMass.value R h2 n m Full hFull).
Local Notation Leb := (@euclidean_lebesgue_measure R n).
Local Notation cell := (fun A hA z => @current_characteristic_density R h2 n m
  Leb (euclidean_lebesgue_is_measure R n) (@euclidean_distribution_measure_borel R n)
  (@euclidean_distribution_measure_compact_finite R n) A hA z).
Variables K C : smooth_compact_set hNX Full.
Variable A : set X.
Hypothesis hA : measure_measurable Leb A.
Hypothesis hAK : A `<=` smooth_compact_carrier K.
Variable z : V.
Local Notation F := (@current_flat_norm R h2 n m Full hFull C).
Local Notation Poly := (@polyhedral_current_subspace R h2 n m Full hFull C).

(** Source for [characteristic_scaled_polyhedral_approximation]:
    every signed multiple of an
    approximable unit cell has the
    same printed approximation property,
    supporting the normalization and scalar
    sign reductions of Federer 4.1.23,
    p. 379. The component approximation
    premise is discharged by the preceding
    unit-cell construction in its consumers. *)
Theorem characteristic_scaled_polyhedral_approximation
    (hApprox : forall delta, 0<delta -> exists P : Current, Poly P /\
      (F (cell A hA z-P)<=delta%:E)%E /\
      (M P<=M (cell A hA z)+delta%:E)%E)
    (c epsilon : R) (hEpsilon : 0<epsilon) :
  exists P : Current, Poly P /\
    (F (cell A hA (c*:z)-P)<=epsilon%:E)%E /\
    (M P<=M (cell A hA (c*:z))+epsilon%:E)%E.
Proof.
case: (eqVneq c 0)=> [->|hC].
- exists 0; split; first exact: subspace_zero.
  rewrite scale0r characteristic_current_coefficient_zero subrr
    current_flat_norm_zero current_mass_zero add0e.
  split; rewrite lee_fin; exact: ltW hEpsilon.
- have hAbs : 0<`|c| by rewrite normr_gt0.
  pose delta := epsilon/`|c|.
  have hDelta : 0<delta := divr_gt0 hEpsilon hAbs.
  have hFactor : `|c|*delta=epsilon by rewrite /delta mulrC divfK // normr_eq0.
  have [P [hPoly [hError hMass]]] := @hApprox delta hDelta.
  have hFiniteError : (F (cell A hA z-P)< +oo)%E := le_lt_trans hError (ltry delta).
  have hScale := @current_flat_finite_scale R h2 n m Full hFull C c
    (cell A hA z-P) hFiniteError.
  have hErrorScaled : (F (cell A hA (c*:z)-c*:P)<=epsilon%:E)%E.
    rewrite characteristic_current_coefficient_scale -scalerBr hScale.
    have h := lee_wpmul2l (x:=`|c|%:E) ltac:(by rewrite lee_fin; exact: normr_ge0 c) hError.
    by rewrite -EFinM hFactor in h.
  have hAFinite : (Leb A< +oo)%E := le_lt_trans
    (measure_mono (euclidean_lebesgue_is_measure R n) hAK)
    (@euclidean_distribution_measure_compact_finite R n (smooth_compact_carrier K)
      (smooth_compact_is_compact K)).
  have hANumber : Leb A \is a fin_num.
    by rewrite (ge0_fin_numE (measure_nonnegative (euclidean_lebesgue_is_measure R n) A)).
  pose a := VN z*fine (Leb A).
  have hBaseMass : M (cell A hA z)=a%:E.
    rewrite (@compact_characteristic_current_properties R h2 n m A hA z K hAK).1
      -(fineK hANumber) -EFinM.
    reflexivity.
  have hScaledMass : M (cell A hA (c*:z))=(`|c|*a)%:E.
    rewrite (@compact_characteristic_current_properties R h2 n m A hA (c*:z) K hAK).1
      (real_seminorm_scale hVN.1) -(fineK hANumber) -EFinM /a mulrA.
    reflexivity.
  have hBoundP : (M P<=(a+delta)%:E)%E by rewrite EFinD -hBaseMass.
  have hMassScaled := @current_finite_mass_scale_bound R h2 n m Full hFull c P
    (a+delta) hBoundP.
  exists (c*:P); split; first exact: (@subspace_scale R Current Poly c P hPoly).
  split; first exact: hErrorScaled.
  rewrite hScaledMass -EFinD.
  have hIdentity : `|c|*(a+delta)=`|c|*a+epsilon by rewrite mulrDr hFactor.
  by rewrite hIdentity in hMassScaled.
Qed.
End ScaledCellApproximation.
