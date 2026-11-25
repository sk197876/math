(** Federer (1969), 3.2.26(3), p. 262: the
    approximate Jacobian of a projection on the tangent plane
    is the projection norm of its unit orientation. Prove the
    intrinsic partial exterior-norm calculation first, using the
    orthonormal-factor laws of 1.7.5–7, pp. 32–34. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import ModuleQuotient Hom TensorUP GrassmannAbbreviations FiniteCoordinates
  EuclideanInnerProduct EuclideanLinearMaps InnerExterior InnerExteriorPositivity InnerNorm
  ExteriorGrading ExteriorMaps ExteriorMapScaling ExteriorNorm ExteriorNormNaturality ExteriorOperatorEstimate
  FiniteExteriorPowers AssociatedSubspace SimpleElementary SimpleProducts SimpleOrthonormalFactor
  OrthonormalFrameMap FrameImageSpan OrthonormalFamilies OrthogonalMaps
  EuclideanProjectionSpace EuclideanProjectionMetric OrthogonalProjectionConstants
  EuclideanLinearJacobian EuclideanTopExteriorVolume PartialFunctionUP PartialExteriorNormUP
  PartialExteriorIsometricChart.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [simple_unit_orthogonal_frame_lift]: supporting
    use of a simple unit m-vector in 3.2.26(3),
    p. 262. Its associated plane is exactly the image
    of an orthogonal injection from R^m; its unit top
    vector has an actual unit preimage. This includes the
    empty exterior product when m=0. *)
Theorem simple_unit_orthogonal_frame_lift (R:realType) m n
    (xi:exterior_power (R_n R n) m):
  simple xi ->exterior_norm (euclidean_two_nonzero R) (@euclidean_inner_productP R n) xi= 1 ->
  exists (f:{linear R_n R m->R_n R n}) (eta:exterior_power (R_n R m) m),
    is_orthogonal_map (@euclidean_inner_product R m) (@euclidean_inner_product R n) f /\
    (forall v,(exists u,f u=v)<->FedererSimple.T xi v) /\
    exterior_power_map f m eta=xi /\
    exterior_norm (euclidean_two_nonzero R) (@euclidean_inner_productP R m) eta= 1.
Proof.
move=>hSimple hUnit.
have hNonzero:xi!=0.
  apply/eqP=>hZero; move:hUnit; rewrite hZero exterior_norm_zero=>/eqP.
  by rewrite eq_sym oner_eq0.
have [e [c [hOrtho [hC hFactor]]]]:=@simple_orthonormal_factor R (euclidean_two_nonzero R)
  (R_n R n) (@euclidean_inner_product R n) (@euclidean_inner_productP R n) m xi hNonzero hSimple.
have [f [hF hFE]]:=orthonormal_frame_map_exists (@euclidean_inner_productP R n) hOrtho.
pose eta:=c*:e_lambda (@coordinate_basis R m) (ord_tuple m).
have hMap:exterior_power_map f m eta=xi.
  rewrite /eta linearZ exterior_map_indexed_product.
  have hFamily:(fun i=>f (@coordinate_basis R m i))=e by apply:funext=>i; exact:hFE.
  rewrite hFamily; exact (esym hFactor).
have hRange v:(exists u,f u=v)<->FedererSimple.T xi v.
  have hWord:e_lambda e (ord_tuple m)!=0.
    apply/eqP=>hZero; by move:hNonzero; rewrite hFactor hZero scaler0 eqxx.
  rewrite (@basis_image_finite_span R (R_n R m) (R_n R n) m
    (@coordinate_basis R m) (@coordinate_basisP R m) e f hFE v).
  rewrite hFactor (@associated_scale_nonzero R (R_n R n) m (e_lambda e (ord_tuple m)) c hC v).
  symmetry; exact:(@product_associated_space R (euclidean_two_nonzero R) (R_n R n) m e hWord v).
have hEta:exterior_norm (euclidean_two_nonzero R) (@euclidean_inner_productP R m) eta= 1.
  have hNatural:=@exterior_norm_orthogonal_natural R (euclidean_two_nonzero R)
    (R_n R m) (R_n R n) (@euclidean_inner_product R m) (@euclidean_inner_product R n)
    (@euclidean_inner_productP R m) (@euclidean_inner_productP R n) f hF m eta.
  rewrite hMap hUnit in hNatural; exact:esym hNatural.
exists f,eta; by split; last split; last split.
Qed.

(** Source for [simple_unit_projection_partial_exterior_norm]:
    the intrinsic norm identity behind the first displayed
    integral in 3.2.26(3), p. 262. Restrict the
    actual projection to T(xi); an orthogonal source chart
    and top exterior volume scaling show its m-dimensional
    operator norm equals |(exterior^m p)xi|. No values
    outside that plane enter the partial graph. *)
Theorem simple_unit_projection_partial_exterior_norm (R:realType) m n
    (xi:exterior_power (R_n R n) m) (p:orthogonal_projection_metric_space R n m)
    (d:partial_function (R_n R n) (R_n R m)):
  simple xi ->exterior_norm (euclidean_two_nonzero R) (@euclidean_inner_productP R n) xi= 1 ->
  (forall v w,partial_function_graph d v w <->
    FedererSimple.T xi v /\euclidean_projection_linear p v=w) ->
  is_partial_exterior_norm m d (projection_norm (euclidean_two_nonzero R) xi p).
Proof.
move=>hSimple hUnit hGraph.
have [f [eta [hF [hRange [hMap hEta]]]]]:=simple_unit_orthogonal_frame_lift hSimple hUnit.
pose D:=hom_of_linear f.
pose H:=hom_of_linear (linear_comp (euclidean_projection_linear p) f).
have hCoordinate v w:partial_function_graph d v w <->exists x,D x=v /\H x=w.
  split.
  - move=>hValue; have [hv hw]:=(hGraph v w).1 hValue.
    have [x hx]:=(hRange v).2 hv.
    exists x; split; first exact hx.
    change (euclidean_projection_linear p (f x)=w); by rewrite hx.
  - move=>[x [hx hw]]; apply:(hGraph v w).2; split.
    + apply:(hRange v).1; by exists x.
    + change (euclidean_projection_linear p v=w); rewrite -hx; exact hw.
have hNorm:=@partial_exterior_isometric_chart_norm R m n m m D H d hF hCoordinate.
have hImage:exterior_power_map (hom_as_linear H) m eta=
    exterior_power_map (euclidean_projection_linear p) m xi.
  have hLinear:exterior_power_map (hom_as_linear H) m eta=
      exterior_power_map (linear_comp (euclidean_projection_linear p) f) m eta.
    apply:exterior_power_map_ext=>x; reflexivity.
  by rewrite hLinear -exterior_power_map_composition hMap.
have hScale:=@euclidean_top_exterior_volume_scale R m m H eta.
rewrite hImage hEta mulr1 in hScale.
have hValue:euclidean_linear_jacobian m H=projection_norm (euclidean_two_nonzero R) xi p.
  exact:esym hScale.
by rewrite hValue in hNorm.
Qed.
