(** Federer (1969), 3.3.4, p. 290: the
    actual orthogonal action on T(U) is jointly
    continuous and transitive. Unit-sphere continuity
    and the exact projective Lipschitz law prove
    continuity without selecting projective representatives. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets functions reals topology.
From Federer Require Import Hom GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct
  InnerNorm InnerMetric SymmetricGrading InnerSymmetricPositivity
  SymmetricSquareGeometry SymmetricSquareLipschitz StructureProjectiveSphere
  StructureProjectiveSpace StructureProjectiveRotation StructureProjectiveTransport
  UnitSphereSpace UnitSphereOrthogonalAction UnitVectorOrthogonalMap OrthogonalGroupHaarMeasure
  EuclideanOrthogonalInvariantMeasures EuclideanOrthogonalBlockExtension OrthogonalMaps
  MetricSubsetBackground NormMetricScaleContinuity
  TopologicalProductMaps IsometricFamilyJointContinuity.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [structure_projective_quotient_continuous]:
    the continuous unit-sphere map T onto the
    actual T(U), Federer 3.3.4, p. 290,
    with inherited source and target metrics. *)
Theorem structure_projective_quotient_continuous (R:realType) m:
  continuous (@structure_projective_quotient R m).
Proof.
pose S:=[the metricType R of metric_subset (@euclidean_unit_sphere_set R m.+1)].
pose M:=structure_projective_space R m.
have hLip:=@inner_projective_square_unit_lipschitz R (R_n R m.+1)
  (@euclidean_inner_product R m.+1) (@euclidean_inner_productP R m.+1)
  (@euclidean_unit_sphere_set R m.+1) (fun x hx=>hx).
apply:(@metric_fixed_lipschitz_continuous R S M (@structure_projective_quotient R m) 1 ler01).
move=>x y; rewrite !metric_subset_distanceE mul1r.
have h:=hLip.2 (val x) (val y) (set_valP x) (set_valP y).
by rewrite mul1r in h.
Qed.

(** Source for [structure_projective_orbit_continuous]:
    continuity of every actual orbit in T(U),
    Federer 3.3.4, p. 290. A representative
    is used only locally in the proof; the
    action remains the symmetric-power action. *)
Theorem structure_projective_orbit_continuous (R:realType) m
    (z:structure_projective_space R m):
  continuous (fun g:euclidean_orthogonal_group R m.+1=>structure_projective_action g z).
Proof.
pose O:=[the topologicalType of set_type (euclidean_orthogonal_group R m.+1)].
pose E:=inner_metric_space (@euclidean_inner_productP R m.+1).
have [x hx hTx]:=set_valP z.
have hPair:continuous (fun g:O=>(g,x):O*E).
  apply:topological_pair_continuous; last exact:cst_continuous.
  by move=>g; exact:cvg_id.
have hEval:continuous (fun g:O=>(orthogonal_element_map g x:E)).
  move=>g; exact:(continuous_comp (hPair g)
    (@euclidean_orthogonal_evaluation_continuous R m.+1 (g,x))).
have hRep (g:O):val (structure_projective_action g z)=
    inner_projective_square (orthogonal_element_map g x).
  change (structure_projective_rotation g (val z)=inner_projective_square (orthogonal_element_map g x)).
  rewrite -hTx; exact:structure_projective_square_natural.
have hUnit (g:O):@euclidean_unit_sphere_set R m.+1 (orthogonal_element_map g x).
  change (inner_norm (@euclidean_inner_productP R m.+1) (orthogonal_element_map g x)= 1).
  by rewrite (orthogonal_map_norm (@euclidean_inner_productP R m.+1)
    (@euclidean_inner_productP R m.+1) (orthogonal_element_orthogonal g)).
have hLip:=@inner_projective_square_unit_lipschitz R (R_n R m.+1)
  (@euclidean_inner_product R m.+1) (@euclidean_inner_productP R m.+1)
  (@euclidean_unit_sphere_set R m.+1) (fun y hy=>hy).
move=>g U hU.
have [e he hBall]:=proj1 (metricType_numDomainType.nbhs_mdistP (structure_projective_action g z) U) hU.
have hNear:nbhs (orthogonal_element_map g x:E)
    [set y:E|mdist (orthogonal_element_map g x:E) y<e].
  apply:(proj2 (metricType_numDomainType.nbhs_mdistP (orthogonal_element_map g x:E) _)).
  by exists e.
have hNbhs:=hEval g _ hNear.
apply:(@filterS O (nbhs g) _
  [set h:O|mdist (orthogonal_element_map g x:E) (orthogonal_element_map h x:E)<e]
  _ _ hNbhs)=>h hh; apply:hBall.
change (is_true (mdist (structure_projective_action g z) (structure_projective_action h z)<e)).
rewrite !metric_subset_distanceE (hRep g) (hRep h).
have hBound:=hLip.2 _ _ (hUnit g) (hUnit h).
rewrite mul1r in hBound.
exact:le_lt_trans hBound hh.
Qed.

(** Source for [structure_projective_action_continuous]:
    joint continuity of the actual action on
    T(U), Federer 3.3.4, p. 290. Every
    point orbit is continuous and all group
    elements have the same isometry bound. *)
Theorem structure_projective_action_continuous (R:realType) m:
  continuous (fun z:euclidean_orthogonal_group R m.+1*structure_projective_space R m=>
    structure_projective_action z.1 z.2).
Proof.
apply:isometric_family_joint_continuous.
- exact:(@structure_projective_action_isometry R m).
- exact:(@structure_projective_orbit_continuous R m).
Qed.

(** Source for [structure_projective_action_transitive]:
    transitivity of the actual action on T(U),
    Federer 3.3.4, p. 290. An actual orthogonal
    map between the two locally witnessed unit
    vectors gives the required group element. *)
Theorem structure_projective_action_transitive (R:realType) m
    (z w:structure_projective_space R m):
  exists g:euclidean_orthogonal_group R m.+1,structure_projective_action g z=w.
Proof.
have [x hx hTx]:=set_valP z; have [y hy hTy]:=set_valP w.
have [f [hf hxy]]:=@unit_vector_orthogonal_map_exists R m.+1 x y (ltn0Sn m) hx hy.
pose g:=orthogonal_element_of (@euclidean_inner_productP R m.+1) (@coordinate_basisP R m.+1) hf.
exists g; apply:val_inj.
change (structure_projective_rotation g (val z)=val w).
rewrite -hTx -hTy /structure_projective_rotation structure_projective_square_natural.
change (inner_projective_square (f x)=inner_projective_square y).
by rewrite hxy.
Qed.
