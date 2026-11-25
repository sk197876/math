(** Actual-space endpoint regressions for Federer (1969),
    4.1.26, pp. 383–384. These use the public
    signed-degree laws and actual sealed current image:
    empty A, identity, a genuine orientation reversal,
    the entire critical fibre of a positive-dimensional
    constant map, and the nonzero R^0 point. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions
  classical_sets reals constructive_ereal topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP NormOpenDomainLaws
  InnerNorm InnerMetric HilbertFormCompactness GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct
  ExteriorGrading EuclideanLinearMaps ExteriorDeterminant OrthogonalMaps EuclideanOrientationReflection
  LipschitzUP LipschitzBasic CurrentSpaces CurrentDensityUP CurrentDensityAction CurrentDensityUniqueness
  CurrentBoundedCharacteristicFlat CurrentFlatLipschitzPushforwardSealed
  EuclideanFundamentalCurrent EuclideanFundamentalCurrentNonzero EuclideanCharacteristicCurrent
  EuclideanLebesgueDimensions MeasureUP MetricDiameter MetricDiameterMaps
  CharacteristicFunctionUP CharacteristicFunctionSealed PartialFunctionUP
  PartialFunctionExtensionUP LipschitzDegreeSealed LipschitzDegreePointValues
  LipschitzDegreeConstantMap LipschitzDegreeCharacteristicImage
  CoveringFamilyUP
  TensorUP
  MeasureSplit
  FiniteExteriorPowers.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [empty_source_signed_degree]: the original
    sum over empty A is zero at
    every target, checking the exact domain of
    the displayed formula in 4.1.26, p. 383. *)
Example empty_source_signed_degree (R:realType) m
    (f:R_n R m->R_n R m) y:
  partial_function_graph (@LipschitzDegree.value R m f set0) y 0.
Proof.
apply:lipschitz_degree_outside_image=>[[x []]].
Qed.

(** Source for [identity_degree_bound]: the actual
    identity differential has norm bound one,
    supporting the identity regression for 4.1.26,
    p. 383. This is only a local test helper. *)
Local Lemma identity_degree_bound (R:realType) m:
  norm_bounded_linear (inner_norm (@euclidean_inner_productP R m))
    (inner_norm (@euclidean_inner_productP R m))
    (hom_of_linear (linear_id (R_n R m))).
Proof.
exists 1;split;first exact:ler01.
by move=>x;rewrite hom_of_linearE /= mul1r.
Qed.

(** Source for [identity_source_signed_degree]: the
    original identity map has degree chi_A
    pointwise, checking both the on-set and
    empty-fibre clauses of 4.1.26, p. 383. *)
Example identity_source_signed_degree (R:realType) m (A:set (R_n R m)) y:
  partial_function_graph (@LipschitzDegree.value R m idfun A) y
    (@CharacteristicFunction.value R (R_n R m) A y).
Proof.
case:(pselect (A y))=>hy.
- rewrite (characteristic_on_set (@CharacteristicFunction.laws R (R_n R m) A) hy).
  have h:=@lipschitz_degree_injective_linear_value R m
    (hom_of_linear (linear_id (R_n R m))) (identity_degree_bound R m)
    (fun x z hx=>hx) A y hy.
  have hDet:euclidean_det (hom_as_linear (hom_of_linear (linear_id (R_n R m))))= 1.
    rewrite -(@euclidean_det_id R m);apply:det_ext=>x;by [].
  by rewrite hDet sgr1 in h.
- rewrite (characteristic_off_set (@CharacteristicFunction.laws R (R_n R m) A) hy).
  apply:lipschitz_degree_outside_image=>[[x hx hxy]].
  by rewrite -hxy in hy.
Qed.

(** Source for [reflected_source_signed_degree]: a genuine
    orthogonal orientation reversal has degree minus
    one at every image point of A,
    checking the sign in 4.1.26, p. 383.
    Such a reflection exists in every positive dimension. *)
Example reflected_source_signed_degree (R:realType) p:
  exists L:Hom (R_n R p.+1) (R_n R p.+1),cancel L L /\
    forall (A:set (R_n R p.+1)) x,A x->
      partial_function_graph (@LipschitzDegree.value R p.+1 L A) (L x) (-1).
Proof.
have[L [hOrthogonal [hInverse hDet]]]:=@euclidean_orientation_reflection_exists R p.+1 (ltn0Sn p).
have hBound:norm_bounded_linear (inner_norm (@euclidean_inner_productP R p.+1))
    (inner_norm (@euclidean_inner_productP R p.+1)) L.
  exists 1;split;first exact:ler01.
  move=>x;rewrite -(@hom_as_linearE R _ _ L x).
  by rewrite (@orthogonal_map_norm R _ _ _ _
    (@euclidean_inner_productP R p.+1) (@euclidean_inner_productP R p.+1)
    (hom_as_linear L) hOrthogonal x) mul1r.
exists L;split;first exact:hInverse.
move=>A x hx.
have h:=@lipschitz_degree_injective_linear_value R p.+1 L hBound
  (can_inj hInverse) A x hx.
have hEuclidean:euclidean_det (hom_as_linear L)= -1:=hDet.
by rewrite hEuclidean sgrN1 in h.
Qed.

(** Source for [constant_critical_fibre_signed_degree]: the
    whole critical fibre of a positive-dimensional
    constant map has signed degree zero,
    even with infinitely many source points,
    checking 4.1.26, p. 383. *)
Example constant_critical_fibre_signed_degree (R:realType) p (A:set (R_n R p.+1)):
  partial_function_graph (@LipschitzDegree.value R p.+1
    (fun _:R_n R p.+1=>0) A) 0 0.
Proof. exact:lipschitz_degree_positive_constant_value. Qed.

(** Source for [zero_degree_whole_bounded]: R^0 is
    one bounded point, supporting the actual
    dimension-zero regression for 4.1.26, p. 383.
    No nonempty source point is selected here. *)
Local Lemma zero_degree_whole_bounded (R:realType):
  @metric_set_bounded R (inner_metric_space (@euclidean_inner_productP R 0%N)) setT.
Proof.
have hWhole:(@setT (R_n R 0%N))=[set 0].
  apply/seteqP;split=>x _;first exact:coordinate_zero;exact:Logic.I.
by rewrite /metric_set_bounded hWhole extended_metric_diameter_singleton ltry.
Qed.

(** Source for [identity_degree_lipschitz]: the actual
    identity is globally one-Lipschitz, supporting
    the nonzero R^0 image regression for
    4.1.26, p. 383. This is only a local helper. *)
Local Lemma identity_degree_lipschitz (R:realType) m:
  @is_metric_lipschitz R (inner_metric_space (@euclidean_inner_productP R m))
    (inner_metric_space (@euclidean_inner_productP R m)) setT idfun.
Proof.
exists 1;split;first exact:ltr01.
split;first exact:ler01;by move=>x y _ _;rewrite mul1r.
Qed.

(** Source for [zero_dimensional_signed_degree_image]: the
    actual nonzero R^0 Euclidean point has
    degree one and its sealed identity image
    is that same nonzero current. This
    checks the full current identity of 4.1.26,
    p. 383, rather than a helper-only scalar formula. *)
Example zero_dimensional_signed_degree_image (R:realType) (h2:(1+1:R)!=0):
  let X:=R_n R 0%N in
  let Full:=fun _:X=>True in
  let hFull:=fun x (_:True)=>norm_full_domain_interior
    (inner_norm (@euclidean_inner_productP R 0%N)) x in
  let hA:=@measure_measurable_whole R X (@euclidean_lebesgue_measure R 0%N)
    (euclidean_lebesgue_is_measure R 0%N) in
  let T:=@euclidean_characteristic_current R h2 0%N Full hA in
  let hFlat:=@current_bounded_characteristic_flat R h2 0%N Full hA (zero_degree_whole_bounded R) in
  let hLocal:=@metric_lipschitz_is_local R
    (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R 0%N)))
    (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R 0%N)))
    Full idfun (identity_degree_lipschitz R 0%N) in
  let Q:=@CurrentFlatLipschitzPushforward.value R h2 0%N 0%N 0%N
    Full Full hFull hFull idfun (fun _ _=>Logic.I) hLocal T hFlat in
  partial_function_graph (@LipschitzDegree.value R 0%N idfun Full) 0 1 /\
    Q=@euclidean_fundamental_current R h2 0%N /\ Q<>0.
Proof.
move=>X Full hFull hA T hFlat hLocal Q.
have hOne:forall x:X,partial_function_graph (@LipschitzDegree.value R 0%N idfun Full) x 1.
  move=>x;have h:=@identity_source_signed_degree R 0%N Full x.
  by rewrite (characteristic_on_set (@CharacteristicFunction.laws R X Full) Logic.I) in h.
have hExt:is_partial_function_total_extension (@LipschitzDegree.value R 0%N idfun Full)
    (fun _=>1:R).
  move=>x a ha;symmetry;exact:partial_function_single_valued ha (hOne x).
have hAction:=@lipschitz_degree_current_action R h2 0%N idfun
  (identity_degree_lipschitz R 0%N) Full hA (zero_degree_whole_bounded R) (fun _=>1) hExt.
have hField:(fun x:X=>(1:R)*:e_lambda (@coordinate_basis R 0%N) (ord_tuple 0%N))=
    (fun _=>e_lambda (@coordinate_basis R 0%N) (ord_tuple 0%N)).
  by apply:funext=>x;rewrite scale1r.
rewrite hField in hAction.
have hEquality:Q=@euclidean_fundamental_current R h2 0%N.
  exact:(@current_density_action_unique R h2 0%N 0%N (@euclidean_lebesgue_measure R 0%N)
    (fun _=>e_lambda (@coordinate_basis R 0%N) (ord_tuple 0%N)) Q
    (@euclidean_fundamental_current R h2 0%N) hAction (@euclidean_fundamental_current_action R h2 0%N)).
split;first exact:hOne 0.
split;first exact:hEquality.
rewrite hEquality;exact:(@euclidean_fundamental_current_nonzero R h2 0%N).
Qed.
