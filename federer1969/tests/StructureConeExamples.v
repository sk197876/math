(** Federer (1969), 3.3.1, p. 287: actual cone regressions
    retain a noncentral line point, the strict finite-radius cutoff,
    the opposite full-rank projection, and zero ambient dimension. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets functions reals constructive_ereal topology.
From Federer Require Import TensorUP ModuleQuotient GrassmannAbbreviations GrassmannSubspaces
  EuclideanInnerProduct InnerMetric InnerNorm FiniteCoordinates
  EuclideanOneCoordinate EuclideanOneNormDifferential CoordinateProjection
  AdjointUP Adjoint OrthogonalMaps OrthogonalInjectionSpaces
  EuclideanOrthogonalInvariantMeasures EuclideanProjectionSpace
  EuclideanGrassmannProbabilityUP EuclideanGrassmannProbability
  StructureConeUP StructureCone StructureConeBasic
  StructureProjectionKernelUP StructureProjectionKernel
  StructureProjectionDistance StructureProjectionCone
  StructureKernelTopology StructureKernelProbability.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [structure_actual_full_line_cone]: concrete
    regression for the definition in Federer 3.3.1, p. 287.
    The actual projection R^1 to R^0 has the whole line as
    kernel; the point one belongs at infinite radius but is
    excluded at radius one, even with the same aperture one half. *)
Example structure_actual_full_line_cone (R:realType):
  exists p:euclidean_projection_space R 1 0,
    structure_cone (structure_projection_kernel (leq0n 1) p)
      0 +oo%E (1/2) (euclidean_one_embed (1:R)) /\
    ~structure_cone (structure_projection_kernel (leq0n 1) p)
      0 1%E (1/2) (euclidean_one_embed (1:R)).
Proof.
have [f hf]:=@euclidean_orthogonal_injection_exists R 1 0 (leq0n 1).
have hp:is_orthogonal_projection (@euclidean_inner_product R 1)
    (@euclidean_inner_product R 0)
    (inner_adjoint (@euclidean_inner_productP R 0)
      (@euclidean_inner_productP R 1) (@coordinate_basisP R 0) f).
  by exists f; split; [exact:hf|exact:inner_adjointP].
pose p:=orthogonal_projection_of (@euclidean_inner_productP R 0)
  (@euclidean_inner_productP R 1) (@coordinate_basisP R 1) hp.
have hZero x:euclidean_projection_linear p x=0.
  by apply/ffunP=>i; have hi:=ltn_ord i; rewrite ltn0 in hi.
have hNorm:inner_norm (@euclidean_inner_productP R 1)
    (euclidean_one_embed (1:R))= 1.
  by rewrite euclidean_one_norm_coordinate /euclidean_one_embed ffunE normr1.
exists p; split.
- apply/(structure_projection_coneE (leq0n 1) p 0 +oo%E (1/2)).
  rewrite subr0 hZero inner_norm0 mulr0 hNorm; split.
  + exact:ltr01.
  + exact:ltry.
- move=>h; have [_ hRadius]:=(structure_projection_coneE (leq0n 1) p 0 1%E (1/2) _).1 h.
  by rewrite subr0 hNorm ltxx in hRadius.
Qed.

(** Source for [structure_actual_identity_cone_excludes_one]:
    the actual identity projection of the line has zero kernel.
    Its point one is outside the aperture-one-half cone at every
    radius, testing the first strict inequality of 3.3.1, p. 287. *)
Example structure_actual_identity_cone_excludes_one (R:realType):
  exists p:euclidean_projection_space R 1 1,
    forall r,~structure_cone (structure_projection_kernel (leqnn 1) p)
      0 r (1/2) (euclidean_one_embed (1:R)).
Proof.
have hp:O_star (linear_id (R_n R 1)).
  exists (linear_id (R_n R 1)); split; by move=>x y.
have [p hEval]:=euclidean_projection_linear_complete hp.
exists p=>r h.
have [hAngle _]:=(structure_projection_coneE (leqnn 1) p 0 r (1/2) _).1 h.
rewrite subr0 hEval !euclidean_one_norm_coordinate /euclidean_one_embed ffunE normr1 in hAngle.
by rewrite mulr1 invf_div divr1 ltrn1 in hAngle.
Qed.

(** Source for [structure_actual_zero_ambient_cone]: the actual
    R^0 endpoint of the definition in Federer 3.3.1, p. 287.
    Every point is the vertex, so the cone is empty for every
    radius and aperture; no positive-dimension premise is added. *)
Example structure_actual_zero_ambient_cone (R:realType)
    (V:G (R_n R 0) 0) (a:inner_metric_space (@euclidean_inner_productP R 0)) r s:
  structure_cone V a r s=set0.
Proof.
apply/seteqP; split=>x hx; last by [].
have he:x=a by apply/ffunP=>i; have hi:=ltn_ord i; rewrite ltn0 in hi.
subst x; exact:(structure_cone_vertex_excluded hx).
Qed.
