(** Federer (1969), 4.1.23, p. 379:
    rotate the original measurable cell to
    the standard coordinate coefficient, apply its
    completed rectangular approximation, and rotate back.
    The whole compact C is transported; no
    convexity or unsupported flat support index is used. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  functions classical_sets reals constructive_ereal topology.
From Federer Require Import Hom AffineMaps RealNormUP NormMetric NormDifferentialUP
  NormOpenDomainLaws NormRegularity InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct FiniteCoordinates FiniteExteriorPowers
  ExteriorGrading ExteriorMaps ExteriorMapScaling OrthogonalMaps EuclideanAffineSmooth
  CurrentSpaces CurrentCoefficientNorms CurrentSupportGeometry CurrentMassSealed
  CurrentCharacteristicDensity CurrentCompactPushforwardAlgebra CurrentFlatNorm
  SmoothCompactSet SmoothCompactImage PolyhedralCurrentAlgebra
  CompactCharacteristicCurrent CharacteristicCurrentAlgebra
  OrthogonalCharacteristicCurrent OrthogonalSmoothCurrentBounds
  OrthogonalApproximationTransport MeasurableStandardCellApproximation
  EuclideanLebesgueDimensions EuclideanDistributionMeasureContext MeasureUP MeasureBasic.
From Federer Require Import TensorUP.
From Federer Require Import ModuleQuotient.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section OrthogonalCellApproximation.
Variable R : realType.
Hypothesis h2 : (1+1:R)!=0.
Variables n m : nat.
Hypothesis hMN : (m<=n)%N.
Local Notation X := (R_n R n).
Local Notation B := (@euclidean_inner_product R n).
Local Notation hB := (@euclidean_inner_productP R n).
Local Notation NX := (inner_norm hB).
Local Notation hNX := (inner_norm_real_norm hB).
Local Notation Full := (fun _ : X => True).
Local Notation hFull := (fun (x : X) (_ : True) => norm_full_domain_interior NX x).
Local Notation Current := (@current_space R h2 n Full hFull m).
Local Notation M := (@CurrentMass.value R h2 n m Full hFull).
Local Notation Leb := (@euclidean_lebesgue_measure R n).
Local Notation cell := (fun A hA z => @current_characteristic_density R h2 n m
  Leb (euclidean_lebesgue_is_measure R n) (@euclidean_distribution_measure_borel R n)
  (@euclidean_distribution_measure_compact_finite R n) A hA z).
Local Notation prefix := (e_lambda (fun i : 'I_m => @coordinate_basis R n
  (widen_ord hMN i)) (ord_tuple m)).
Variables f g : {linear X->X}.
Hypotheses (hF : is_orthogonal_map B B f) (hG : is_orthogonal_map B B g).
Hypotheses (hFG : cancel f g) (hGF : cancel g f).
Variable u : exterior_power X m.
Hypothesis hCoordinate : exterior_power_map f m u=prefix.
Variables K C : smooth_compact_set hNX Full.
Hypothesis hKC : forall x, smooth_compact_carrier K x ->
  norm_domain_interior NX (smooth_compact_carrier C) x.
Variable A : set X.
Hypothesis hA : measure_measurable Leb A.
Hypothesis hAK : A `<=` smooth_compact_carrier K.
Local Notation T := (cell A hA u).
Local Notation image := (fun (x : X) (_ : True) => Logic.I).
Local Notation hf := (@euclidean_affine_map_smooth R n n Full hFull f (linear_affine_map f)).
Local Notation hg := (@euclidean_affine_map_smooth R n n Full hFull g (linear_affine_map g)).

(** Source for [orthogonal_cell_polyhedral_approximation]:
    the original measurable cell whose
    coefficient rotates to the standard
    unit vector has the printed
    polyhedral approximation in C,
    Federer 4.1.23, p. 379.
    The map inverse, all image conditions,
    compact carriers and mass comparisons
    are used internally in the construction. *)
Theorem orthogonal_cell_polyhedral_approximation epsilon (hEpsilon : 0<epsilon) :
  exists P : Current, @polyhedral_current_subspace R h2 n m Full hFull C P /\
    (@current_flat_norm R h2 n m Full hFull C (T-P)<=epsilon%:E)%E /\
    (M P<=M T+epsilon%:E)%E.
Proof.
pose KF := @smooth_compact_image R X X NX NX hNX hNX Full Full f image
  (norm_class_continuous (hf 0%N)) K.
pose CF := @smooth_compact_image R X X NX NX hNX hNX Full Full f image
  (norm_class_continuous (hf 0%N)) C.
have hKCF y : smooth_compact_carrier KF y ->
    norm_domain_interior NX (smooth_compact_carrier CF) y.
  move=> [x hx <-]; have [r [hr hBall]] := @hKC x hx.
  exists r; split; first exact: hr.
  move=> v hv; exists (x+g v).
  - apply: hBall; by rewrite (@orthogonal_map_norm R X X B B hB hB g hG v).
  - by rewrite linearD (@hGF v).
have hBackIndex y : smooth_compact_carrier CF y -> smooth_compact_carrier C (g y).
  move=> [x hx <-]; by rewrite (@hFG x).
pose hFA := @orthogonal_characteristic_current_image_measurable R n A hA f hF.
have hFAKF : (f @` A) `<=` smooth_compact_carrier KF.
  move=> y [x hx <-]; exists x; [exact: (@hAK x hx)|reflexivity].
pose S := cell (f @` A) hFA prefix.
have hSupportS := (@compact_characteristic_current_properties R h2 n m
  (f @` A) hFA prefix KF hFAKF).2.
pose hCompactS := @current_support_compact_bound R h2 n m Full hFull KF S hSupportS.
have hCompactT := @orthogonal_characteristic_current_compact R h2 n m A hA u K hAK.
have hAFinite : (Leb A< +oo)%E := le_lt_trans
  (measure_mono (euclidean_lebesgue_is_measure R n) hAK)
  (@euclidean_distribution_measure_compact_finite R n (smooth_compact_carrier K)
    (smooth_compact_is_compact K)).
have hANumber : Leb A \is a fin_num.
  by rewrite (ge0_fin_numE (measure_nonnegative (euclidean_lebesgue_is_measure R n) A)).
have hTFinite : (M T< +oo)%E.
  rewrite (@compact_characteristic_current_properties R h2 n m A hA u K hAK).1
    -(fineK hANumber) -EFinM.
  exact: ltry.
have hForward := @orthogonal_characteristic_current_pushforward R h2 n m
  A hA u K hAK f hF hCompactT.
rewrite hCoordinate in hForward.
have hMassCompare := @orthogonal_compact_current_mass_bound R h2 n m f hF
  T hCompactT hTFinite.
rewrite hForward in hMassCompare.
have hSFinite : (M S< +oo)%E := le_lt_trans hMassCompare hTFinite.
have hBackCoefficient : exterior_power_map g m prefix=u.
  rewrite -hCoordinate exterior_power_map_composition.
  have hMaps : forall x, linear_comp g f x=linear_id X x by move=> x; exact: hFG x.
  rewrite (@exterior_power_map_ext R X X (linear_comp g f) (linear_id X) hMaps m u).
  exact: exterior_power_map_identity.
pose hBackA := @orthogonal_characteristic_current_image_measurable R n (f @` A) hFA g hG.
have hBackSet : g @` (f @` A)=A.
  apply: funext=> x; apply: propext; split.
  - move=> [y [z hz <-] <-]; by rewrite (@hFG z).
  - move=> hx; exists (f x); first by exists x.
    exact: hFG x.
have hRecovery := @orthogonal_characteristic_current_pushforward R h2 n m
  (f @` A) hFA prefix KF hFAKF g hG hCompactS.
rewrite hBackCoefficient in hRecovery.
have hCellBack : cell (g @` (f @` A)) hBackA u=T.
  exact: characteristic_current_set_congruence hBackSet.
rewrite hCellBack in hRecovery.
have [P [hPoly [hError hMass]]] := @measurable_standard_cell_polyhedral_approximation
  R h2 n m hMN KF CF hKCF (f @` A) hFA hFAKF epsilon hEpsilon.
exact: (@orthogonal_polyhedral_approximation_transport R h2 n m g hG CF C hBackIndex
  S T hCompactS
  (fun x hx => @norm_domain_interior_member R X NX hNX (smooth_compact_carrier CF) x
    (@hKCF x (@hSupportS x hx))) hSFinite hRecovery hMassCompare
  epsilon P hPoly hError hMass).
Qed.
End OrthogonalCellApproximation.
