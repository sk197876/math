(** Federer (1969), 3.2.27, p. 263: the norm
    of a coordinate exterior projection is the absolute
    Grassmann coordinate in the orthonormal exterior basis.
    Prove the identity through the abstract exterior adjoint
    and the one-dimensional target top power. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct EuclideanLinearMaps
  InnerProductUP InnerNorm InnerExterior InnerExteriorPositivity InnerExteriorBasis ExteriorNorm
  ExteriorGrading ExteriorMaps ExteriorMapScaling ExteriorOperatorEstimate ExteriorAdjoint TopExteriorNorm ExteriorDeterminant
  FiniteExteriorPowers ExteriorIndices SimpleAdaptedBasis CoordinateProjection BasisInterpolation Bilinear TensorUP
  EuclideanProjectionSpace EuclideanProjectionMetric OrthogonalProjectionConstants ProjectionNormalVector.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [coordinate_exterior_projection_norm]: the
    coordinate absolute value in 3.2.27, p. 263,
    from the exterior orthonormal basis of 1.7.5,
    p. 32, and the exterior-adjoint equation of
    1.7.6, p. 33. No simplicity hypothesis is needed. *)
Lemma coordinate_exterior_projection_norm (R:realType) n m (lambda:Lambda n m)
    (xi:exterior_power (R_n R n) m):
  exterior_norm (euclidean_two_nonzero R) (@euclidean_inner_productP R m)
    (exterior_power_map (GRing.Linear.clone _ _ _ _ (@coordinate_projection R n m lambda) _) m xi)=
  `|exterior_inner_form (euclidean_two_nonzero R) (@euclidean_inner_productP R n)
    xi (@coordinate_e_lambda R n m lambda)|.
Proof.
pose F:=GRing.Linear.clone _ _ _ _ (@coordinate_projection R n m lambda) _.
pose G:=@coordinate_injection R n m lambda.
pose omega:=@top_vector R m (R_n R m) (@coordinate_basis R m).
have hUnit:=@euclidean_coordinate_top_vector_unit R m.
change (exterior_norm (euclidean_two_nonzero R) (@euclidean_inner_productP R m) omega= 1) in hUnit.
have hNonzero:omega!=0.
  by rewrite -(exterior_norm_eq0 (euclidean_two_nonzero R) (@euclidean_inner_productP R m)) hUnit oner_eq0.
have [c hC]:=@nonzero_top_vector_spans R (euclidean_two_nonzero R) (R_n R m) m
  (@coordinate_basis R m) (@coordinate_basisP R m) omega hNonzero (exterior_power_map F m xi).
have hImage:exterior_power_map G m omega=@coordinate_e_lambda R n m lambda.
  rewrite /omega /top_vector /finite_e_lambda exterior_map_indexed_product /coordinate_e_lambda
    (@indexed_productE R (Choice.clone 'I_n _) (R_n R n) (@coordinate_basis R n) m (val lambda)).
  change (e_lambda (fun i:'I_m=>G (@coordinate_basis R m i)) (ord_tuple m)=
    e_lambda (fun i:'I_m=>@coordinate_basis R n (tnth (val lambda) i)) (ord_tuple m)).
  have hFamily:(fun i:'I_m=>G (@coordinate_basis R m i))=
      (fun i:'I_m=>@coordinate_basis R n (tnth (val lambda) i)).
    apply:funext=>i; rewrite /G /coordinate_injection basis_interpolationE; reflexivity.
  by rewrite hFamily.
have hAdj:=@exterior_power_adjoint R (euclidean_two_nonzero R) (R_n R n) (R_n R m)
  (@euclidean_inner_product R n) (@euclidean_inner_product R m)
  (@euclidean_inner_productP R n) (@euclidean_inner_productP R m) F G
  (@coordinate_projection_adjoint R n m lambda) m xi omega.
rewrite hImage hC (bilZl (@exterior_inner_form_bilinear R (euclidean_two_nonzero R)
  (R_n R m) (@euclidean_inner_product R m) (@euclidean_inner_productP R m) m)) /= in hAdj.
have hSquare:exterior_inner_form (euclidean_two_nonzero R) (@euclidean_inner_productP R m) omega omega= 1.
  by rewrite -exterior_norm_square hUnit expr1n.
change (exterior_inner_form (euclidean_two_nonzero R) (@euclidean_inner_productP R n)
    xi (@coordinate_e_lambda R n m lambda)=
  (c*exterior_inner_form (euclidean_two_nonzero R) (@euclidean_inner_productP R m) omega omega)%R) in hAdj.
rewrite hSquare mulr1 in hAdj.
by rewrite hC exterior_norm_scale hUnit mulr1 -hAdj.
Qed.

(** Source for [coordinate_projection_parameter_exists]: the
    p_lambda family in 3.2.27, p. 262, represented
    in the existing abstract compact projection space.
    Existence follows from its complete O* interface;
    the coordinate evaluation law is the specification. *)
Lemma coordinate_projection_parameter_exists (R:realType) n m (lambda:Lambda n m):
  exists p:orthogonal_projection_metric_space R n m,
    forall x,euclidean_projection_linear p x=@coordinate_projection R n m lambda x.
Proof.
exact:(@euclidean_projection_linear_complete R n m
  (GRing.Linear.clone _ _ _ _ (@coordinate_projection R n m lambda) _)
  (@coordinate_projection_orthogonal R n m lambda)).
Qed.

(** Source for [coordinate_parameter_projection_norm]: the
    absolute Grassmann coordinate of T in 3.2.27,
    p. 263, for any projection parameter satisfying
    the actual coordinate-map law. No implementation of
    the projection parameter is exposed downstream. *)
Lemma coordinate_parameter_projection_norm (R:realType) n m (lambda:Lambda n m)
    (p:orthogonal_projection_metric_space R n m):
  (forall x,euclidean_projection_linear p x=@coordinate_projection R n m lambda x) ->
  forall xi:exterior_power (R_n R n) m,
    projection_norm (euclidean_two_nonzero R) xi p=
    `|exterior_inner_form (euclidean_two_nonzero R) (@euclidean_inner_productP R n)
      xi (@coordinate_e_lambda R n m lambda)|.
Proof.
move=>hP xi; rewrite /projection_norm
  (@exterior_power_map_ext R (R_n R n) (R_n R m) (euclidean_projection_linear p)
    (GRing.Linear.clone _ _ _ _ (@coordinate_projection R n m lambda) _) hP m xi).
exact:coordinate_exterior_projection_norm.
Qed.
