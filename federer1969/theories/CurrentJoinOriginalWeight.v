(** Federer (1969), 4.1.11, p. 365: the literal
    partial orientation weight in the first mass display.
    Both original maximal orienting fields retain their
    domains; their auxiliary total densities do not define
    the weight. The scalar factor is separated only by
    the existing bilinearity and mass-norm laws. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions
  classical_sets reals constructive_ereal topology.
From Federer Require Import Hom TensorUP Bilinear ExtendedRealOrderTopology RealNormUP NormMetric
  NormDifferentialUP NormOpenDomainLaws InnerNorm HilbertFormCompactness GrassmannAbbreviations
  EuclideanInnerProduct ExteriorGrading ExteriorPowers ExteriorHomogeneousProducts
  CurrentDomain CurrentSpaces CurrentCoefficientNorms CurrentIntegrationCriterion CurrentOrientationSealed
  CurrentJoinDomain CurrentJoinRawCoordinates ScalarUnitMixedPower
  PartialFunctionUP PartialFunctionBasic PartialFunctionPair PartialFunctionPostcomposition
  PartialFunctionPrecomposition SummableRealFunctionUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section CurrentJoinOriginalWeight.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n i j:nat.
Local Notation X := (R_n R n).
Local Notation Full := (fun _:X=>True).
Local Notation hFull := (fun (x:X) (_:True)=>@norm_full_domain_interior R X
  (inner_norm (@euclidean_inner_productP R n)) x).
Local Notation CT := (current_domain R (n+(1+n))%N (@current_join_domain R n)).
Local Notation first := (@current_join_first_point R n).
Local Notation last := (@current_join_last_point R n).
Local Notation time := (@current_join_time_coordinate R n).
Local Notation V := (exterior_power X (i+(1+j))%N).
Local Notation N := (@current_vector_mass R h2 n (i+(1+j))%N).

(** Source for [current_join_spatial_vector]: the original
    time-independent vector xi wedge (y-x) wedge eta in
    the second mass display, Federer 4.1.11, p. 365. *)
Definition current_join_spatial_vector (z:CT) (a:exterior_power X i) (b:exterior_power X j):V:=
  exterior_product a (exterior_product
    (exterior_first_inclusion X (set_val (last z)-set_val (first z))) b).

(** Source for [current_join_original_vector]: the original
    vector (1-t)^i xi wedge (y-x) wedge t^j eta in the
    first mass display, Federer 4.1.11, p. 365. *)
Definition current_join_original_vector (z:CT) (a:exterior_power X i) (b:exterior_power X j):V:=
  exterior_product ((1-time z)^+i*:a) (exterior_product
    (exterior_first_inclusion X (set_val (last z)-set_val (first z))) (time z^+j*:b)).

(** Source for [current_join_original_vector_scale]: the
    exact scalar mixed power factors out of the original
    triple wedge, supporting equality of the mass displays
    in Federer 4.1.11, p. 365. *)
Lemma current_join_original_vector_scale z a b:
  current_join_original_vector z a b=
    @scalar_unit_mixed_power R i j (time z)*:current_join_spatial_vector z a b.
Proof.
rewrite /current_join_original_vector /current_join_spatial_vector
  (bilZl (@exterior_product_bilinear R X i (1+j)%N))
  (bilZr (@exterior_product_bilinear R X 1%N j))
  (bilZr (@exterior_product_bilinear R X i (1+j)%N)) scalerA.
by [].
Qed.

(** Source for [current_join_original_vector_mass]: the
    original vector mass is the absolute mixed power
    times the original spatial wedge mass, supporting
    Federer 4.1.11, p. 365. This identity holds at all
    real times; the time measure is concentrated on [0,1]. *)
Lemma current_join_original_vector_mass z a b:
  N (current_join_original_vector z a b)=
    `|@scalar_unit_mixed_power R i j (time z)|*N (current_join_spatial_vector z a b).
Proof.
by rewrite current_join_original_vector_scale
  (real_seminorm_scale (@current_vector_mass_real_norm R h2 n (i+(1+j))%N).1).
Qed.

Variable S:@current_space R h2 n Full hFull i.
Variable T:@current_space R h2 n Full hFull j.
Hypothesis hS:@is_integration_representable_current R h2 n i Full hFull S.
Hypothesis hT:@is_integration_representable_current R h2 n j Full hFull T.
Local Notation OS := (@CurrentOrientation.value R h2 n i Full hFull S hS).
Local Notation OT := (@CurrentOrientation.value R h2 n j Full hFull T hT).

(** Source for [current_join_original_weight]: the literal
    mass weight in Federer 4.1.11, p. 365, on exactly
    the common pulled-back domains of the two original
    orienting fields. No values outside those domains are supplied. *)
Definition current_join_original_weight:partial_function CT (extended_real_line R):=
  partial_function_postcompose
    (partial_function_pair (partial_function_total (fun z:CT=>z))
      (partial_function_pair (partial_function_precompose first OS)
        (partial_function_precompose last OT)))
    (fun zab:CT*(exterior_power X i*exterior_power X j)=>
      (N (current_join_original_vector zab.1 zab.2.1 zab.2.2))%:E).

(** Source for [current_join_original_weight_graph]: the
    original weight has precisely the printed wedge mass
    wherever both original orienting fields are defined,
    supporting Federer 4.1.11, p. 365. *)
Lemma current_join_original_weight_graph z v:
  partial_function_graph current_join_original_weight z v<->
  exists a,exists b,partial_function_graph OS (first z) a /\
    partial_function_graph OT (last z) b /\
    (N (current_join_original_vector z a b))%:E=v.
Proof.
split.
- move=>[[u [a b]] [[hPoint [hA hB]] hValue]].
  have hzu:z=u:=hPoint;subst u.
  exists a,b;split;first exact:hA.
  split;[exact:hB|exact:hValue].
- move=>[a [b [hA [hB hValue]]]].
  exists (z,(a,b));split;first by split;[|split].
  exact:hValue.
Qed.

(** Source for [current_join_original_weight_domain]: the
    original partial weight keeps both original orientation
    domains, supporting Federer 4.1.11, p. 365. *)
Lemma current_join_original_weight_domain:
  partial_function_domain current_join_original_weight=
    [set z:CT|partial_function_domain OS (first z) /\partial_function_domain OT (last z)].
Proof.
rewrite /current_join_original_weight partial_function_postcompose_domain
  !partial_function_pair_domain partial_function_total_domain setTI
  !partial_function_precompose_domain.
by [].
Qed.
End CurrentJoinOriginalWeight.
