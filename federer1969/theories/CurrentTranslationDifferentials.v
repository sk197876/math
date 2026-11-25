(** Federer (1969), 4.1.18, p. 374: actual
    differentials of the original translation homotopies.
    The parameter map's whole spatial derivative is
    q+t p, but its derivative on the x factor
    is exactly identity. This retains the sharp
    coefficient without a false bound for the
    whole (z,x) source.  *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  functions classical_sets reals.
From Federer Require Import Hom TensorUP RealNormUP NormDifferentialUP
  NormDifferentialLinear NormDifferentialArithmetic NormDifferentialLocal NormFiniteLinearBound NormOpenDomainLaws
  InnerNorm HilbertFormCompactness GrassmannAbbreviations FiniteCoordinates
  EuclideanInnerProduct EuclideanOneCoordinate EuclideanBlockCoordinates EuclideanBlockLinearMaps
  EuclideanCartesianMap ExteriorGrading ExteriorMaps ExteriorMapScaling
  CurrentSpaces CurrentMapDifferential CurrentDiracDensity CurrentCartesianVectorProduct
  CurrentZeroDegreeExteriorLaws CurrentHomotopyUP CurrentHomotopyTimeVelocity
  CurrentAffineHomotopySealed CurrentAffineHomotopyDifferential
  CurrentTranslationHomotopy CurrentTranslationParameterHomotopy
  CurrentTranslations EuclideanAdditiveGroup.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Section CurrentTranslationDifferentials.
Variable R:realType.
Variable n:nat.
Local Notation X:=(R_n R n).
Local Notation Z:=(R_n R (n+n)%N).
Local Notation NX:=(inner_norm (@euclidean_inner_productP R n)).
Local Notation NZ:=(inner_norm (@euclidean_inner_productP R (n+n)%N)).
Local Notation hNX:=(inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation hNZ:=(inner_norm_real_norm (@euclidean_inner_productP R (n+n)%N)).
Local Notation Full:=(fun _:X=>True).
Local Notation FullZ:=(fun _:Z=>True).
Local Notation hFull:=(fun (x:X) (_:True)=>norm_full_domain_interior NX x).
Local Notation hFullZ:=(fun (a:Z) (_:True)=>norm_full_domain_interior NZ a).
Local Notation p:=(@euclidean_first_block_map R n n).
Local Notation q:=(@euclidean_last_block_map R n n).
Local Notation Q:=(@euclidean_last_injection_map R n n).
Local Notation unit:=(@current_scalar_multivector_unit R n).
Local Notation H:=(@current_translation_parameter_homotopy R n).
Local Notation hH:=(@current_translation_parameter_homotopy_laws R n).

(** Source for [current_translation_parameter_slice_differential]:
    D H_t=q+t p, supporting the literal velocity
    integrand of 4.1.18, p. 374. *)
Theorem current_translation_parameter_slice_differential t a:
  @current_map_differential R (n+n)%N n FullZ
    (@current_homotopy_slice_map R (n+n)%N n H t) a=q+t*:p.
Proof.
pose L:Hom Z X:=q+t*:p.
have hBound:=@norm_finite_linear_bounded R Z X NZ NX hNZ hNX
  (n+n)%N (@coordinate_basis R (n+n)%N) (@coordinate_basisP R (n+n)%N) L.
have hD:=@norm_differential_linear R Z X NZ NX hNZ hNX FullZ a L
  (hFullZ a Logic.I) hBound.
apply:(@current_map_differential_unique R (n+n)%N n FullZ
  (@current_homotopy_slice_map R (n+n)%N n H t) a L).
apply:(@norm_differential_domain_agreement R Z X NZ NX hNZ FullZ L
  (@current_homotopy_slice_map R (n+n)%N n H t) a L _ hD)=>y _.
rewrite /current_homotopy_slice_map current_translation_parameter_homotopy_coordinates.
change (q y+t*:p y=
  q ((@euclidean_block_split R 1%N (n+n)%N
    (euclidean_block_join (euclidean_one_embed t,y))).2)+
  (@euclidean_one_project R ((@euclidean_block_split R 1%N (n+n)%N
    (euclidean_block_join (euclidean_one_embed t,y))).1))*:
  p ((@euclidean_block_split R 1%N (n+n)%N
    (euclidean_block_join (euclidean_one_embed t,y))).2)).
by rewrite euclidean_block_joinK euclidean_one_embedK.
Qed.

(** Source for [current_translation_parameter_velocity]:
    the original homotopy's time velocity is z,
    Federer 4.1.18, p. 374. *)
Theorem current_translation_parameter_velocity t z x:
  @current_homotopy_time_velocity R (n+n)%N n (fun _=>True) FullZ H
    t (euclidean_block_join (z,x))=z.
Proof.
have hAffine:forall s a,(fun _:R=>True) s->FullZ a->
    @current_homotopy_slice_map R (n+n)%N n H s a=
    (1-s)*:q a+s*:(@current_translation_parameter_end R n a).
  move=>s a _ _;exact:(@CurrentAffineHomotopy.laws R (n+n)%N n q
    (@current_translation_parameter_end R n) s a).
rewrite (@current_affine_homotopy_time_velocity R (n+n)%N n (fun _=>True)
  FullZ Full q (@current_translation_parameter_end R n) H hH hAffine
  t (euclidean_block_join (z,x)) Logic.I Logic.I).
rewrite /current_translation_parameter_end hom_addE addrAC subrr add0r.
change ((@euclidean_block_split R n n (euclidean_block_join (z,x))).1=z).
by rewrite euclidean_block_joinK.
Qed.

(** Source for [current_translation_parameter_spatial_exterior_identity]:
    the zero-degree parameter factor contributes its
    scalar unit and every spatial multivector is
    unchanged, supporting 4.1.18, pp. 374–375. *)
Theorem current_translation_parameter_spatial_exterior_identity j t a
    (eta:exterior_power X j):
  exterior_power_map (hom_as_linear
    (@current_map_differential R (n+n)%N n FullZ
      (@current_homotopy_slice_map R (n+n)%N n H t) a)) j
    (@current_cartesian_vector_product R n n 0%N j unit eta)=eta.
Proof.
rewrite current_translation_parameter_slice_differential
  /current_cartesian_vector_product /current_scalar_multivector_unit
  exterior_power_map_zeroth_scalar exterior_product_zeroth_scalar_left scale1r
  exterior_power_map_composition.
have hComp:linear_comp (hom_as_linear (q+t*:p)) (hom_as_linear Q)=1 (linear_id X).
  move=>v.
  change (@euclidean_last_block R n n (@euclidean_last_injection R n n v)+
    t*:@euclidean_first_block R n n (@euclidean_last_injection R n n v)=v).
  by rewrite euclidean_last_block_injectionK euclidean_first_block_last_injection scaler0 addr0.
rewrite (@exterior_power_map_ext R X X _ (linear_id X) hComp j eta).
exact:exterior_power_map_identity.
Qed.

Variable z:X.
Local Notation Hz:=(@current_translation_homotopy R n z).
Local Notation hHz:=(@current_translation_homotopy_laws R n z).
Local Notation tau:=(@euclidean_translation R n z).
Local Notation Id:=(hom_of_linear (@linear_id R X)).

(** Source for [current_translation_slice_differential]:
    the original H^z_t has identity spatial
    differential at every time and point,
    Federer 4.1.18, p. 374. *)
Theorem current_translation_slice_differential t x:
  @current_map_differential R n n Full
    (@current_homotopy_slice_map R n n Hz t) x=Id.
Proof.
have hBound:norm_bounded_linear NX NX Id.
  exists 1;split;first exact:ler01.
  by move=>v;change (is_true (NX v<=1*NX v));rewrite mul1r.
have hKnown:=@norm_differential_linear R X X NX NX hNX hNX Full x Id
  (hFull x Logic.I) hBound.
have hConstant:=@norm_differential_constant R X X NX NX hNX hNX Full x
  (t*:z) (hFull x Logic.I).
have hSum:=@norm_differential_add R X X NX NX hNX Full
  (fun y:X=>y) (fun _:X=>t*:z) x Id 0 hKnown hConstant.
rewrite addr0 in hSum.
apply:(@current_map_differential_unique R n n Full
  (@current_homotopy_slice_map R n n Hz t) x Id).
apply:(@norm_differential_domain_agreement R X X NX NX hNX Full
  (fun y:X=>y+t*:z) (@current_homotopy_slice_map R n n Hz t) x Id _ hSum)=>y _.
rewrite /current_homotopy_slice_map current_translation_homotopy_coordinates.
change (y+t*:z=
  (@euclidean_block_split R 1%N n (euclidean_block_join (euclidean_one_embed t,y))).2+
  (@euclidean_one_project R ((@euclidean_block_split R 1%N n
    (euclidean_block_join (euclidean_one_embed t,y))).1))*:z).
by rewrite euclidean_block_joinK euclidean_one_embedK.
Qed.

(** Source for [current_translation_velocity]: the actual
    original time velocity is z, including z=0,
    Federer 4.1.18, p. 374. *)
Theorem current_translation_velocity t x:
  @current_homotopy_time_velocity R n n (fun _=>True) Full Hz t x=z.
Proof.
have hAffine:forall s a,(fun _:R=>True) s->Full a->
    @current_homotopy_slice_map R n n Hz s a=(1-s)*:a+s*:tau a.
  move=>s a _ _;exact:(@CurrentAffineHomotopy.laws R n n (fun y:X=>y) tau s a).
rewrite (@current_affine_homotopy_time_velocity R n n (fun _=>True)
  Full Full (fun y:X=>y) tau Hz hHz hAffine t x Logic.I Logic.I).
by rewrite /euclidean_translation addrK.
Qed.
End CurrentTranslationDifferentials.
