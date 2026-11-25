(** Federer (1969), 3.4.12, p. 339, extending the prescribed
    joint coordinates of 3.4.8(10), pp. 331–332. Assemble the
    original prefix and equations as a holomorphic map. The existing
    linear postcomposition and differential uniqueness laws recover
    its coordinate differentials; the proved inverse theorem applies. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import Hom TensorUP Bilinear RealNormUP ScalarRestriction ComplexScalarSealed ComplexNormUP
  ComplexModulus ComplexScalarNorm ComplexOrderedBases FiniteCoordinates StandardHermitian
  HermitianRealImaginary InnerNorm HolomorphicCoordinateNorm FieldBlockLinearMaps
  FieldCoordinateFunctional NormDifferentialUP NormDifferentialLinear NormDifferentialLocal
  NormDifferentialFiniteCalculus NormDifferentialDirectional NormFiniteLinearBound NormOpenDomainLaws
  NormClassOneUP NormRegularity NormAnalyticLocal NormDiffeomorphismUP
  HolomorphicUP HolomorphicLinear HolomorphicArithmetic HolomorphicFiniteCalculus
  HolomorphicScalarAssembly FiniteHolomorphicInversePoint.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section JointInverse.
Variable R:realType.
Variables m l:nat.
Local Notation C:=(ComplexScalars.C R).
Local Notation X:=(coordinate_space C (m+l)).
Local Notation Y:=(coordinate_space C m).
Local Notation Z:=(coordinate_space C l).
Local Notation XR:=(restricted_space (ComplexScalars.embed R) X).
Local Notation YR:=(restricted_space (ComplexScalars.embed R) Y).
Local Notation ZR:=(restricted_space (ComplexScalars.embed R) Z).
Local Notation CR:=(restricted_space (ComplexScalars.embed R) C^o).
Local Notation NX:=(@holomorphic_coordinate_norm R (m+l)).
Local Notation NY:=(@holomorphic_coordinate_norm R m).
Local Notation NZ:=(@holomorphic_coordinate_norm R l).
Local Notation hNX:=(complex_norm_real (@holomorphic_coordinate_norm_laws R (m+l))).
Local Notation hNY:=(complex_norm_real (@holomorphic_coordinate_norm_laws R m)).
Local Notation hNZ:=(complex_norm_real (@holomorphic_coordinate_norm_laws R l)).
Local Notation NC:=(@complex_modulus R).
Local Notation hNC:=(@complex_modulus_real_norm R).
Variable A:set X.
Hypothesis hA:forall x,A x ->@norm_domain_interior R XR NX A x.
Variable P:Hom X Y.
Hypothesis hP:@norm_bounded_linear R XR YR NX NY (complex_hom_real P).
Variable f:'I_l->X->C.
Hypothesis hF:forall j,@is_holomorphic R X C^o NX NC hNX hNC A (f j).
Variable a:X.
Hypothesis ha:A a.
Variable D:'I_l->Hom XR CR.
Hypothesis hD:forall j,@has_norm_differential R XR CR NX NC A (f j) a (D j).
Hypothesis hSeparate:forall u,P u=0 ->(forall j,D j u=0) ->u=0.

(** Source for [finite_holomorphic_joint_inverse]: the original
    prefix remains the first coordinate block, and the original
    equations remain the last block of an actual local holomorphic
    diffeomorphism, 3.4.12, p. 339. The joint kernel condition
    proves injectivity of the actual differential; no inverse or
    coordinate differential formula is assumed. *)
Theorem finite_holomorphic_joint_inverse:
  exists (H G:X->X) r,
    (forall x,@field_first_block_map C m l (H x) = P x) /\
    (forall x j,@field_last_block_map C m l (H x) j=f j x) /\
    @is_holomorphic R X X NX NX hNX hNX A H /\0<r /\
    (forall x,NX (x-a)<r ->A x) /\
    is_norm_diffeomorphism hNX hNX [set x|NX (x-a)<r]
      (H @` [set x|NX (x-a)<r]) H G 1%N /\
    @is_holomorphic R X X NX NX hNX hNX (H @` [set x|NX (x-a)<r]) G.
Proof.
pose F:=fun x:X=>[ffun j:'I_l=>f j x].
have hFHol:=@holomorphic_scalar_assembly R l X NX hNX A f hA hF.
pose I:=@field_first_injection_map C m l.
pose J:=@field_last_injection_map C m l.
pose p:=@field_first_block_map C m l.
pose q:=@field_last_block_map C m l.
have hI:=@norm_finite_linear_bounded R YR XR NY NX hNY hNX (m+m)
  (ordered_real_basis (@coordinate_basis C m)) (ordered_real_basisP (@coordinate_basisP C m))
  (complex_hom_real I).
have hJ:=@norm_finite_linear_bounded R ZR XR NZ NX hNZ hNX (l+l)
  (ordered_real_basis (@coordinate_basis C l)) (ordered_real_basisP (@coordinate_basisP C l))
  (complex_hom_real J).
pose H:=fun x:X=>I (P x)+J (F x).
have hFirstHol:=@holomorphic_bounded_linear R X X NX NX hNX hNX A (hom_comp I P)
  hA (norm_bounded_linear_compose hP hI).
have hJHol:=@holomorphic_bounded_linear R Z X NZ NX hNZ hNX setT J
  (fun z _=>@norm_full_domain_interior R ZR NZ z) hJ.
have hLastHol:=@holomorphic_compose_on R X Z X NX NZ NX hNX hNZ hNX A setT
  F J (fun _ _=>Logic.I) hFHol hJHol.
have hH:@is_holomorphic R X X NX NX hNX hNX A H:=holomorphic_add hFirstHol hLastHol.
have hHFirst x:p (H x) = P x.
  rewrite /H linearD /= /I /J /p field_first_block_injectionK field_first_block_last_injection.
  exact:addr0.
have hHLast x:q (H x)=F x.
  rewrite /H linearD /= /I /J /q field_last_block_first_injection field_last_block_injectionK.
  exact:add0r.
have [DH hDH]:=(norm_class_firstP hNX hNX A H).1 (norm_analytic_class_all_orders hH.1 1%N).
pose L:=DH a.
have hL:@has_norm_differential R XR XR NX NX A H a L:=norm_class_one_differential hDH ha.
have hpBound:=@norm_finite_linear_bounded R XR YR NX NY hNX hNY (m+l+(m+l))
  (ordered_real_basis (@coordinate_basis C (m+l))) (ordered_real_basisP (@coordinate_basisP C (m+l)))
  (complex_hom_real p).
have hpD:=@norm_differential_postcompose R XR XR YR NX NX NY hNX A H a L
  (complex_hom_real p) hL hpBound.
have hpActual:@has_norm_differential R XR YR NX NY A P a
    (hom_comp (complex_hom_real p) L).
  apply:(@norm_differential_domain_agreement R XR YR NX NY hNX A _ _ a
    (hom_comp (complex_hom_real p) L) _ hpD)=>x _;exact:hHFirst x.
have hPActual:=@norm_differential_linear R XR YR NX NY hNX hNY A a
  (complex_hom_real P) (@hA a ha) hP.
have hpEqual:=norm_differential_unique hNX hNY hpActual hPActual.
have hLFirst u:p (L u) = P u.
  exact:(congr1 (fun M:Hom XR YR=>M u) hpEqual).
have hLLast u j:q (L u) j=D j u.
  pose c:=hom_comp (@field_coordinate_functional C l j) q.
  have hcBound:=@norm_finite_linear_bounded R XR CR NX NC hNX hNC (m+l+(m+l))
    (ordered_real_basis (@coordinate_basis C (m+l))) (ordered_real_basisP (@coordinate_basisP C (m+l)))
    (complex_hom_real c).
  have hcD:=@norm_differential_postcompose R XR XR CR NX NX NC hNX A H a L
    (complex_hom_real c) hL hcBound.
  have hcActual:@has_norm_differential R XR CR NX NC A (f j) a
      (hom_comp (complex_hom_real c) L).
    apply:(@norm_differential_domain_agreement R XR CR NX NC hNX A _ _ a
      (hom_comp (complex_hom_real c) L) _ hcD)=>x _.
    change (q (H x) j=f j x);by rewrite hHLast /F ffunE.
  have hcEqual:=norm_differential_unique hNX hNC hcActual (hD j).
  exact:(congr1 (fun M:Hom XR CR=>M u) hcEqual).
have hKernel u (hu:L u=0):u=0.
  have hPrefix:P u=0 by rewrite -(hLFirst u) hu linear0.
  apply:(@hSeparate u hPrefix)=>j.
  rewrite -(hLLast u j) hu linear0;by rewrite ffunE.
have hInjective:injective L.
  move=>u v hEqual.
  have hZero:L (u-v)=0 by rewrite (linB (hom_linear L)) hEqual subrr.
  apply/eqP;by rewrite -subr_eq0 (hKernel (u-v) hZero) eqxx.
have [r [hR [hInside [G [hInverse [_ hG]]]]]]:=
  @finite_holomorphic_inverse_from_point_differential R X
    (hermitian_real_part (@standard_hermitian_product R (m+l)))
    (hermitian_real_inner_product (@standard_hermitian_productP R (m+l))) hNX
    (m+l)%N (@coordinate_basis C (m+l)) (@coordinate_basisP C (m+l)) A H a L
    hH ha hL hInjective.
exists H,G,r;split;first exact:hHFirst.
split;first by move=>x j;rewrite hHLast /F ffunE.
split;first exact:hH.
split;first exact:hR.
split;first exact:hInside.
by split.
Qed.
End JointInverse.
