(** Federer (1969), 4.1.18, p. 374: addition
    acts as translation in each fixed kernel fibre.
    On the original zero-current first factor its
    exterior differential is the identity on the
    second factor, preserving sharp constants. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  functions classical_sets reals.
From Federer Require Import Hom TensorUP RealNormUP NormDifferentialUP
  NormDifferentialLinear NormOpenDomainLaws NormFiniteLinearBound NormRegularity NormRegularityOperations
  InnerNorm HilbertFormCompactness GrassmannAbbreviations FiniteCoordinates
  EuclideanInnerProduct EuclideanBlockCoordinates EuclideanBlockLinearMaps EuclideanCartesianMap
  ExteriorGrading ExteriorMaps ExteriorMapScaling AlternatingForms AlternatingDual AlternatingPairing
  CurrentSpaces CurrentDiracDensity CurrentZeroDegreeExteriorLaws CurrentCartesianDomain
  CurrentCartesianVectorProduct CurrentTranslationParameterHomotopy
  SmoothFormPullbackUP SmoothFormPullbackSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section CurrentAdditionZeroFactorPullback.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n j:nat.
Local Notation X:=(R_n R n).
Local Notation Z:=(R_n R (n+n)).
Local Notation NX:=(inner_norm (@euclidean_inner_productP R n)).
Local Notation NZ:=(inner_norm (@euclidean_inner_productP R (n+n))).
Local Notation hNX:=(inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation hNZ:=(inner_norm_real_norm (@euclidean_inner_productP R (n+n))).
Local Notation Full:=(fun _:X=>True).
Local Notation hFull:=(fun (x:X) (_:True)=>norm_full_domain_interior NX x).
Local Notation AB:=(@euclidean_cartesian_set R n n Full Full).
Local Notation hAB:=(@current_cartesian_domain_open R n n Full Full hFull hFull).
Local Notation Add:=(@current_translation_parameter_end R n).
Local Notation Image:=(fun (z:Z) (_:AB z)=>Logic.I).
Local Notation Q:=(@euclidean_last_injection_map R n n).
Local Notation unit:=(@current_scalar_multivector_unit R n).

(** Source for [current_addition_product_smooth]: the
    original addition endpoint is smooth on the
    actual full Cartesian domain, supporting 4.1.18,
    p. 374. *)
Theorem current_addition_product_smooth:
  norm_class_all_orders hNZ hNX AB Add.
Proof.
move=>k;apply:(@norm_class_linear R Z X NZ NX hNZ hNX AB Add k hAB).
exact:(@norm_finite_linear_bounded R Z X NZ NX hNZ hNX (n+n)%N
  (@coordinate_basis R (n+n)%N) (@coordinate_basisP R (n+n)%N) Add).
Qed.

(** Source for [current_addition_product_coordinates]: the
    original endpoint has exactly the literal x+z
    values of 4.1.18, p. 374. *)
Theorem current_addition_product_coordinates z x:
  Add (@euclidean_block_join R n n (z,x))=x+z.
Proof.
rewrite /current_translation_parameter_end hom_addE.
change ((@euclidean_block_split R n n (euclidean_block_join (z,x))).2+
  (@euclidean_block_split R n n (euclidean_block_join (z,x))).1=x+z).
by rewrite euclidean_block_joinK.
Qed.

(** Source for [current_addition_last_exterior_identity]:
    the original zero first degree contributes only
    its scalar unit; the addition differential is
    identity on every spatial multivector. This
    supports the exact constants of 4.1.18,
    pp. 374–375, without bounding the whole source
    operator norm by one. *)
Theorem current_addition_last_exterior_identity (eta:exterior_power X j):
  exterior_power_map (hom_as_linear Add) j
    (@current_cartesian_vector_product R n n 0%N j unit eta)=eta.
Proof.
rewrite /current_cartesian_vector_product /current_scalar_multivector_unit
  exterior_power_map_zeroth_scalar exterior_product_zeroth_scalar_left scale1r
  exterior_power_map_composition.
have hComposition:linear_comp (hom_as_linear Add) (hom_as_linear Q)=1
    (linear_id X).
  move=>v.
  change (Add (@euclidean_last_injection R n n v)=v).
  rewrite /current_translation_parameter_end hom_addE.
  change (@euclidean_last_block R n n (@euclidean_last_injection R n n v)+
    @euclidean_first_block R n n (@euclidean_last_injection R n n v)=v).
  by rewrite euclidean_last_block_injectionK euclidean_first_block_last_injection addr0.
rewrite (@exterior_power_map_ext R X X
  (linear_comp (hom_as_linear Add) (hom_as_linear Q)) (linear_id X)
  hComposition j eta).
exact:exterior_power_map_identity.
Qed.

(** Source for [current_addition_zero_factor_pullback]:
    the literal translated form coefficient in the
    first averaging display of Federer 4.1.18,
    p. 374. Every original form degree is
    retained, including zero and above dimension. *)
Theorem current_addition_zero_factor_pullback
    (omega:@current_smooth_space R h2 n Full hFull j) z x eta:
  pairing (@current_cartesian_vector_product R n n 0%N j unit eta)
    (@current_smooth_value R h2 (n+n)%N AB hAB j
      (@SmoothFormPullback.operator R h2 (n+n)%N n j AB Full hAB hFull
        Add Image current_addition_product_smooth omega)
      (euclidean_block_join (z,x)))=
  pairing eta (@current_smooth_value R h2 n Full hFull j omega (x+z)).
Proof.
have hBound:=@norm_finite_linear_bounded R Z X NZ NX hNZ hNX (n+n)%N
  (@coordinate_basis R (n+n)%N) (@coordinate_basisP R (n+n)%N) Add.
have hPoint:AB (euclidean_block_join (z,x)) by split.
have hD:=@norm_differential_linear R Z X NZ NX hNZ hNX AB
  (euclidean_block_join (z,x)) Add (@current_cartesian_domain_open R n n Full Full hFull hFull
    (euclidean_block_join (z,x)) hPoint) hBound.
rewrite (@smooth_form_pullback_values R (n+n)%N n j AB Full _ _
  (@current_smooth_value R h2 n Full hFull j)
  (@current_smooth_value R h2 (n+n)%N AB hAB j) Add _
  (@SmoothFormPullback.laws R h2 (n+n)%N n j AB Full hAB hFull
    Add Image current_addition_product_smooth)
  omega (euclidean_block_join (z,x)) Add hPoint hD).
rewrite A_m_dual_pairing current_addition_last_exterior_identity
  current_addition_product_coordinates.
reflexivity.
Qed.
End CurrentAdditionZeroFactorPullback.
