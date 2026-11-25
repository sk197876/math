(** Federer (1969), 4.1.23, p. 380:
    the current of a coordinate rectangle
    with separated constant coefficients is
    exactly the Cartesian product of its
    factor currents. Reuse the original
    full mixed-degree product characterisation and
    the preceding Lebesgue subset Fubini law. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  functions classical_sets reals constructive_ereal topology.
From Federer Require Import Hom Bilinear RealNormUP NormMetric NormDifferentialUP
  NormOpenDomainLaws InnerNorm HilbertFormCompactness GrassmannAbbreviations
  EuclideanInnerProduct EuclideanBlockCoordinates EuclideanBlockLinearMaps
  EuclideanCartesianMap ExteriorGrading AlternatingForms AlternatingPairing
  CurrentSpaces CurrentCharacteristicDensity CurrentDensityAction
  CurrentDegreeTransport CurrentOpenRestriction CurrentOpenRestrictionIdentity
  CurrentCartesianDomain CurrentCartesianProductUP CurrentCartesianProductSealed
  CurrentCartesianProductUnique CurrentCartesianTestProductSealed
  CurrentCartesianTestProductEverywhere CurrentCartesianVectorProduct
  CurrentCartesianVectorPairing CurrentCartesianVectorOffDiagonal
  CurrentAmbientCartesianProduct EuclideanLebesgueDimensions
  EuclideanDistributionMeasureContext EuclideanCartesianSubsetIntegral
  MeasureUP MeasureIntegralUP MeasureSubsetIntegral MeasureIntegralUniqueness
  MeasureCharacteristicIntegral SummableRealFunctionUP SummableRealArithmetic
  CharacteristicFunctionUP CharacteristicFunctionSealed
  RealSubsetCharacteristicIntegral RealSubsetIntegralGraph.
From Federer Require Import LatticeL1ApproximationLaws.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [characteristic_density_subset_action]:
    the literal constant-coefficient cell current
    acts by its original subset integral,
    supporting the rectangle reduction of
    Federer 4.1.23, pp. 379–380.
    No finiteness or support premise
    is added to the original measurable set. *)
Theorem characteristic_density_subset_action (R : realType)
    (h2 : (1+1:R)!=0) n m (E : set (R_n R n))
    (hE : measure_measurable (@euclidean_lebesgue_measure R n) E)
    (u : exterior_power (R_n R n) m)
    (phi : @current_test_space R h2 n (fun _ => True)
      (fun (x : R_n R n) (_ : True) => norm_full_domain_interior
        (inner_norm (@euclidean_inner_productP R n)) x) m) :
  let hFull := fun (x : R_n R n) (_ : True) => norm_full_domain_interior
    (inner_norm (@euclidean_inner_productP R n)) x in
  let T := @current_characteristic_density R h2 n m (@euclidean_lebesgue_measure R n)
    (euclidean_lebesgue_is_measure R n) (@euclidean_distribution_measure_borel R n)
    (@euclidean_distribution_measure_compact_finite R n) E hE u in
  is_measure_subset_integral (@euclidean_lebesgue_measure R n) E
    (real_total_integrand (fun x => pairing u
      (@current_test_value R h2 n (fun _ => True) hFull m phi x)))
    (@current_value R h2 n (fun _ => True) hFull m T phi)%:E.
Proof.
move=> hFull T.
have h := @current_characteristic_density_action R h2 n m (@euclidean_lebesgue_measure R n)
  (euclidean_lebesgue_is_measure R n) (@euclidean_distribution_measure_borel R n)
  (@euclidean_distribution_measure_compact_finite R n) E hE u phi.
have hFunction : (fun x => pairing (@CharacteristicFunction.value R (R_n R n) E x*:u)
    (@current_test_value R h2 n (fun _ => True) hFull m phi x))=
    (fun x => @CharacteristicFunction.value R (R_n R n) E x*
      pairing u (@current_test_value R h2 n (fun _ => True) hFull m phi x)).
  apply: funext=> x; exact: (bilZl (@pairing_bilinear R (R_n R n) R^o m)).
rewrite hFunction in h.
exact: (@real_subset_characteristic_integral R (R_n R n) (@euclidean_lebesgue_measure R n)
  E (@CharacteristicFunction.value R (R_n R n) E)
  (fun x => pairing u (@current_test_value R h2 n (fun _ => True) hFull m phi x))
  _ (@CharacteristicFunction.laws R (R_n R n) E)).2 h.
Qed.

Section CharacteristicProduct.
Variable R : realType.
Hypothesis h2 : (1+1:R)!=0.
Variables m n i j : nat.
Local Notation X := (R_n R m).
Local Notation Y := (R_n R n).
Local Notation Z := (R_n R (m+n)).
Local Notation Full := (fun d : nat => fun _ : R_n R d => True).
Local Notation hFull := (fun (d : nat) (x : R_n R d) (_ : True) =>
  norm_full_domain_interior (inner_norm (@euclidean_inner_productP R d)) x).
Local Notation AB := (@euclidean_cartesian_set R m n (Full m) (Full n)).
Local Notation hAB := (@current_cartesian_domain_open R m n (Full m) (Full n)
  (hFull m) (hFull n)).
Local Notation Pure := (fun k l => @CartesianTestProduct.value R h2 m n
  (Full m) (Full n) (hFull m) (hFull n) k l).
Variables (E : set X) (F : set Y).
Hypothesis hE : measure_measurable (@euclidean_lebesgue_measure R m) E.
Hypothesis hF : measure_measurable (@euclidean_lebesgue_measure R n) F.
Local Notation EF := (@euclidean_cartesian_set R m n E F).
Hypothesis hEF : measure_measurable (@euclidean_lebesgue_measure R (m+n)) EF.
Variables (u : exterior_power X i) (v : exterior_power Y j).
Local Notation w := (@current_cartesian_vector_product R m n i j u v).
Local Notation T := (@current_characteristic_density R h2 m i (@euclidean_lebesgue_measure R m)
  (euclidean_lebesgue_is_measure R m) (@euclidean_distribution_measure_borel R m)
  (@euclidean_distribution_measure_compact_finite R m) E hE u).
Local Notation S := (@current_characteristic_density R h2 n j (@euclidean_lebesgue_measure R n)
  (euclidean_lebesgue_is_measure R n) (@euclidean_distribution_measure_borel R n)
  (@euclidean_distribution_measure_compact_finite R n) F hF v).
Local Notation Q := (@current_characteristic_density R h2 (m+n) (i+j)
  (@euclidean_lebesgue_measure R (m+n)) (euclidean_lebesgue_is_measure R (m+n))
  (@euclidean_distribution_measure_borel R (m+n))
  (@euclidean_distribution_measure_compact_finite R (m+n)) EF hEF w).
Local Notation Restrict := (@current_open_restriction R h2 (m+n) (i+j)
  AB (Full (m+n)) hAB (hFull (m+n)) (fun _ _ => Logic.I)).
Local Notation Extend := (@current_open_test_extension R h2 (m+n) (i+j)
  AB (Full (m+n)) hAB (hFull (m+n)) (fun _ _ => Logic.I)).

(** Source for [characteristic_cartesian_current]:
    the exact identity T=R times S
    at the start of the rectangle
    construction, Federer 4.1.23, p. 380.
    The statement permits arbitrary separated
    multivector degrees, constant coefficients and
    measurable factor sets with measurable product. *)
Theorem characteristic_cartesian_current :
  @current_ambient_cartesian_product R h2 m n i j T S=Q.
Proof.
have hLaws : @is_current_cartesian_product R h2 m n (Full m) (Full n)
    (hFull m) (hFull n) Pure i j T S (Restrict Q).
  split.
  - move=> alpha beta.
    have hTI := @characteristic_density_subset_action R h2 m i E hE u alpha.
    have hSI := @characteristic_density_subset_action R h2 n j F hF v beta.
    have hProduct := @euclidean_separated_subset_integral R m n E F
      (fun x => pairing u (@current_test_value R h2 m (Full m) (hFull m) i alpha x))
      (fun x => pairing v (@current_test_value R h2 n (Full n) (hFull n) j beta x))
      (@current_value R h2 m (Full m) (hFull m) i T alpha)
      (@current_value R h2 n (Full n) (hFull n) j S beta) hTI hSI.
    have hQI := @characteristic_density_subset_action R h2 (m+n) (i+j)
      EF hEF w (Extend (Pure i j alpha beta)).
    have hFunction : (fun z => pairing w (@current_test_value R h2 (m+n)
        (Full (m+n)) (hFull (m+n)) (i+j) (Extend (Pure i j alpha beta)) z))=
        (fun z => pairing u (@current_test_value R h2 m (Full m) (hFull m) i alpha
            (euclidean_block_split z).1)*
          pairing v (@current_test_value R h2 n (Full n) (hFull n) j beta
            (euclidean_block_split z).2)).
      apply: funext=> z; rewrite current_open_test_extension_values
        current_cartesian_test_product_values_all.
      exact: current_cartesian_vector_pairing.
    cbn zeta in hQI; rewrite hFunction in hQI.
    rewrite current_open_restriction_evaluation.
    exact: EFin_inj (measure_integral_unique hQI hProduct).
  - move=> k l e hKI alpha beta.
    pose psi := @current_test_degree_transport R h2 (m+n) AB hAB
      (k+l) (i+j) e (Pure k l alpha beta).
    have hQI := @characteristic_density_subset_action R h2 (m+n) (i+j)
      EF hEF w (Extend psi).
    have hFunction : (fun z => pairing w (@current_test_value R h2 (m+n)
        (Full (m+n)) (hFull (m+n)) (i+j) (Extend psi) z))=(fun _ : Z => 0).
      apply: funext=> z; rewrite current_open_test_extension_values /psi
        current_test_degree_transport_values current_cartesian_test_product_values_all.
      exact: (@current_cartesian_vector_off_diagonal R h2 m n i j k l e u v
        (@current_test_value R h2 m (Full m) (hFull m) k alpha (euclidean_block_split z).1)
        (@current_test_value R h2 n (Full n) (hFull n) l beta (euclidean_block_split z).2) hKI).
    cbn zeta in hQI; rewrite hFunction in hQI.
    have hZero := @real_total_zero_integral R Z (@euclidean_lebesgue_measure R (m+n))
      (euclidean_lebesgue_is_measure R (m+n)).
    have hSubset := (@real_subset_integral_total R Z (@euclidean_lebesgue_measure R (m+n))
      EF (fun _ => 0) (fun _ => 0) (0:R)%:E (fun _ _ => erefl) (fun _ _ => erefl)).2 hZero.
    rewrite current_open_restriction_evaluation.
    exact: EFin_inj (measure_integral_unique hQI hSubset).
have hRaw := @current_cartesian_product_unique R h2 m n i j (Full m) (Full n)
  (hFull m) (hFull n) T S _ (Restrict Q)
  (@CartesianCurrentProduct.laws R h2 m n i j (Full m) (Full n) (hFull m) (hFull n) T S)
  hLaws.
rewrite /current_ambient_cartesian_product hRaw.
exact: (@current_equal_domain_restriction_identity R h2 (m+n) (i+j) AB (Full (m+n))
  hAB (hFull (m+n)) (@current_cartesian_full_domain R m n) (fun _ _ => Logic.I) Q).
Qed.
End CharacteristicProduct.
