(** Federer (1969), 4.1.18, p. 374: the
    original parameter transgression on its zero-degree
    parameter factor is the fixed-z transgression.
    Prove equality from the literal old velocity
    integrals, with no interchange of current-valued
    Banach integrals.  *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  functions classical_sets reals constructive_ereal topology.
From Federer Require Import Hom TensorUP RealNormUP NormDifferentialUP NormOpenDomainLaws
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  EuclideanOneCoordinate EuclideanBlockCoordinates EuclideanBlockLinearMaps EuclideanCartesianMap
  ExteriorGrading ExteriorPowers ExteriorHomogeneousProducts ExteriorMaps ExteriorMapScaling AlternatingForms AlternatingPairing CurrentSpaces CurrentMapDifferential
  CurrentDiracDensity CurrentCartesianVectorProduct CurrentHomotopyUP CurrentHomotopyTimeVelocity CurrentHomotopyDomain
  CurrentHomotopyTransgressionSealed CurrentHomotopyTransgressionVelocity
  CurrentTranslationHomotopy CurrentTranslationParameterHomotopy CurrentTranslationDifferentials
  CurrentTranslations EuclideanAdditiveGroup RealMetricBackground LebesgueScalarMeasure
  MeasureSubsetIntegral MeasureIntegralUniqueness RealSubsetIntegralAgreement.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section CurrentTranslationTransgressionFibre.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n j:nat.
Local Notation X:=(R_n R n).
Local Notation Z:=(R_n R (n+n)%N).
Local Notation Full:=(fun _:X=>True).
Local Notation FullZ:=(fun _:Z=>True).
Local Notation H:=(@current_translation_parameter_homotopy R n).
Local Notation hH:=(@current_translation_parameter_homotopy_laws R n).
Local Notation q:=(@euclidean_last_block_map R n n).
Local Notation End:=(@current_translation_parameter_end R n).
Local Notation hSource:=(@current_homotopy_source_open R (n+n)%N n
  (fun _=>True) FullZ Full q End H hH.1).
Local Notation hTarget:=(@current_homotopy_target_open R (n+n)%N n
  (fun _=>True) FullZ Full q End H hH.1).
Local Notation F:=(@current_smooth_space R h2 n Full hTarget (1+j)%N).
Local Notation fv:=(@current_smooth_value R h2 n Full hTarget (1+j)%N).
Local Notation pv:=(@current_smooth_value R h2 (n+n)%N FullZ hSource j).
Local Notation KH:=(@CurrentHomotopyTransgression.value R h2 (n+n)%N n j
  (fun _=>True) FullZ Full q End H hH).
Local Notation unit:=(@current_scalar_multivector_unit R n).
Variable z:X.
Local Notation Hz:=(@current_translation_homotopy R n z).
Local Notation hHz:=(@current_translation_homotopy_laws R n z).
Local Notation tau:=(@euclidean_translation R n z).
Local Notation hSourceZ:=(@current_homotopy_source_open R n n
  (fun _=>True) Full Full (fun y:X=>y) tau Hz hHz.1).
Local Notation hTargetZ:=(@current_homotopy_target_open R n n
  (fun _=>True) Full Full (fun y:X=>y) tau Hz hHz.1).
Local Notation Fz:=(@current_smooth_space R h2 n Full hTargetZ (1+j)%N).
Local Notation fzv:=(@current_smooth_value R h2 n Full hTargetZ (1+j)%N).
Local Notation zv:=(@current_smooth_value R h2 n Full hSourceZ j).
Local Notation Kz:=(@CurrentHomotopyTransgression.value R h2 n n j
  (fun _=>True) Full Full (fun y:X=>y) tau Hz hHz).
Local Notation I:=(`[0,1]:set (real_line_metric R)).

(** Source for [current_translation_transgression_fibre]:
    after the zero-degree kernel coordinate is fixed,
    the original averaged homotopy integrand is exactly
    z wedge eta paired with omega(x+t z),
    Federer 4.1.18, p. 374. Equal target
    presentations are compared by their actual values. *)
Theorem current_translation_transgression_fibre
    (omega:F) (omegaZ:Fz):
  (forall y,fv omega y=fzv omegaZ y)->
  forall x (eta:exterior_power X j),
  pairing (@current_cartesian_vector_product R n n 0%N j unit eta)
    (pv (KH omega) (euclidean_block_join (z,x)))=
  pairing eta (zv (Kz omegaZ) x).
Proof.
move=>hTargetMatch x eta.
have hParam:=@current_homotopy_transgression_velocity_integral R h2 (n+n)%N n j
  (fun _=>True) FullZ Full q End H hH omega
  (euclidean_block_join (z,x)) Logic.I
  (@current_cartesian_vector_product R n n 0%N j unit eta).
have hFixed:=@current_homotopy_transgression_velocity_integral R h2 n n j
  (fun _=>True) Full Full (fun y:X=>y) tau Hz hHz omegaZ x Logic.I eta.
have hId:hom_as_linear (hom_of_linear (@linear_id R X)) =1 (@linear_id R X).
  by move=>v;reflexivity.
have hExteriorIdentity:
    exterior_power_map (hom_as_linear (hom_of_linear (@linear_id R X))) j eta=eta.
  rewrite (@exterior_power_map_ext R X X _ (linear_id X) hId j eta).
  exact:exterior_power_map_identity.
have hPoint t:I t->
    pairing (exterior_product
      (exterior_first_inclusion X
        (@current_homotopy_time_velocity R (n+n)%N n (fun _=>True) FullZ H
          t (euclidean_block_join (z,x))))
      (exterior_power_map (hom_as_linear
        (@current_map_differential R (n+n)%N n FullZ
          (@current_homotopy_slice_map R (n+n)%N n H t) (euclidean_block_join (z,x)))) j
        (@current_cartesian_vector_product R n n 0%N j unit eta)))
      (fv omega (H (euclidean_block_join
        (euclidean_one_embed t,euclidean_block_join (z,x)))))=
    pairing (exterior_product
      (exterior_first_inclusion X
        (@current_homotopy_time_velocity R n n (fun _=>True) Full Hz t x))
      (exterior_power_map (hom_as_linear
        (@current_map_differential R n n Full
          (@current_homotopy_slice_map R n n Hz t) x)) j eta))
      (fzv omegaZ (Hz (euclidean_block_join (euclidean_one_embed t,x)))).
  move=>ht.
  rewrite current_translation_parameter_velocity
    current_translation_parameter_spatial_exterior_identity
    current_translation_velocity current_translation_slice_differential
    hExteriorIdentity.
  have hParamPoint:H (euclidean_block_join
      (euclidean_one_embed t,euclidean_block_join (z,x)))=x+t*:z.
    rewrite current_translation_parameter_homotopy_coordinates.
    change (q ((@euclidean_block_split R 1%N (n+n)%N
        (euclidean_block_join (euclidean_one_embed t,euclidean_block_join (z,x)))).2)+
      @euclidean_one_project R ((@euclidean_block_split R 1%N (n+n)%N
        (euclidean_block_join (euclidean_one_embed t,euclidean_block_join (z,x)))).1)*:
      @euclidean_first_block_map R n n ((@euclidean_block_split R 1%N (n+n)%N
        (euclidean_block_join (euclidean_one_embed t,euclidean_block_join (z,x)))).2)=x+t*:z).
    rewrite euclidean_block_joinK euclidean_one_embedK.
    change ((@euclidean_block_split R n n (euclidean_block_join (z,x))).2+
      t*:((@euclidean_block_split R n n (euclidean_block_join (z,x))).1)=x+t*:z).
    by rewrite euclidean_block_joinK.
  have hFixedPoint:Hz (euclidean_block_join (euclidean_one_embed t,x))=x+t*:z.
    rewrite current_translation_homotopy_coordinates.
    change ((@euclidean_block_split R 1%N n
      (euclidean_block_join (euclidean_one_embed t,x))).2+
      @euclidean_one_project R ((@euclidean_block_split R 1%N n
        (euclidean_block_join (euclidean_one_embed t,x))).1)*:z=x+t*:z).
    by rewrite euclidean_block_joinK euclidean_one_embedK.
  by rewrite hParamPoint hFixedPoint hTargetMatch.
have hSame:=@real_subset_integral_agreement R (real_line_metric R)
  (@lebesgue_scalar_measure R) I _ _ _ hPoint hParam.
exact:(EFin_inj (measure_integral_unique hSame hFixed)).
Qed.
End CurrentTranslationTransgressionFibre.
