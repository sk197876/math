(** Federer (1969), 3.3.1, p. 287: dist(x,ker p)=|p(x)|.
    Prove both infimum laws from the actual orthogonal adjoint;
    no nearest point or distance identity is an extra premise. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals topology.
From Federer Require Import Hom ModuleQuotient GrassmannAbbreviations GrassmannSubspaces
  EuclideanInnerProduct InnerProductUP InnerNorm InnerMetric OrthogonalMaps AdjointUP
  AdjointLaws EuclideanRectangularAdjoint OrthogonalInjectionSpaces EuclideanProjectionSpace
  ProjectionNorm MetricSetDistanceUP MetricSetDistanceBasic StructureProjectionKernelUP
  StructureProjectionKernel.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section ProjectionDistance.
Variable R:realType.
Variables n m:nat.
Variable p:euclidean_projection_space R n m.
Local Notation hN:=(@euclidean_inner_productP R n).
Local Notation hM:=(@euclidean_inner_productP R m).
Local Notation L:=(euclidean_projection_linear p).
Local Notation A:=(euclidean_rectangular_adjoint (orthogonal_projection_map p)).

(** Source for [structure_projection_adjoint_pairing]: supporting
    the distance identity of Federer 3.3.1, p. 287, by the
    adjoint equation of 1.7.4, p. 30, for the original projection. *)
Lemma structure_projection_adjoint_pairing x y:
  euclidean_inner_product x (A y)=euclidean_inner_product (L x) y.
Proof. exact:euclidean_rectangular_adjoint_pairing. Qed.

(** Source for [structure_projection_adjoint_orthogonal]: the
    adjoint of the projection is an orthogonal injection, 1.7.4,
    p. 30, used for the distance assertion in 3.3.1, p. 287.
    Its defining witness is used only locally to identify the
    existing opaque adjoint through its pairing law. *)
Lemma structure_projection_adjoint_orthogonal x y:
  euclidean_inner_product (A x) (A y)=euclidean_inner_product x y.
Proof.
have [f [hf hPair]]:=orthogonal_projection_map_projection p.
have hA z:A z=f z.
  apply:(inner_vectors_ext hN)=>w.
  rewrite structure_projection_adjoint_pairing (inner_symmetric hM (L w) z).
  rewrite (hPair z w).
  exact:(inner_symmetric hN (f z) w).
rewrite (hA x) (hA y); exact:hf.
Qed.

(** Source for [structure_projection_adjointE]: symmetric form
    of the same pairing in Federer 3.3.1, p. 287, supporting
    the closest-point calculation in the actual kernel. *)
Lemma structure_projection_adjointE y x:
  euclidean_inner_product y (L x)=euclidean_inner_product (A y) x.
Proof.
rewrite (inner_symmetric hM y (L x)) -structure_projection_adjoint_pairing.
exact:(inner_symmetric hN x (A y)).
Qed.

(** Source for [structure_projection_adjoint_cancel]: p p*=identity,
    1.7.4, p. 30, applied to the actual p of 3.3.1, p. 287. *)
Lemma structure_projection_adjoint_cancel y:L (A y)=y.
Proof.
apply:(inner_vectors_ext hM)=>z.
by rewrite structure_projection_adjointE structure_projection_adjoint_orthogonal.
Qed.

(** Source for [structure_projection_residual_kernel]: the
    actual residual x-p*p(x) belongs to ker p, supporting
    the distance equality in Federer 3.3.1, p. 287. *)
Lemma structure_projection_residual_kernel x:L (x-A (L x))=0.
Proof. by rewrite linearB structure_projection_adjoint_cancel subrr. Qed.

(** Source for [structure_projection_residual_distance]: the
    distance of x from its residual is |p(x)| by the isometry
    of p*, supporting Federer 3.3.1, p. 287. *)
Lemma structure_projection_residual_distance
    (x:inner_metric_space hN):
  mdist x (x-A (L x))=inner_norm hM (L x).
Proof.
rewrite inner_metric_distanceE opprB addrCA subrr addr0.
exact:(orthogonal_map_norm hM hN
  (f:=hom_as_linear A) structure_projection_adjoint_orthogonal (L x)).
Qed.

(** Source for [structure_projection_distance_laws]: both
    independent infimum laws for dist(x,ker p)=|p(x)|,
    Federer 3.3.1, p. 287. Contraction gives the lower
    bound and the actual kernel residual gives attainment. *)
Theorem structure_projection_distance_laws (K:G (R_n R n) (n-m)):
  is_structure_projection_kernel p K ->
  is_metric_set_distance
    [set x:inner_metric_space hN|grassmann_val K x]
    (fun x=>inner_norm hM (L x)).
Proof.
move=>hK; constructor.
- move=>x w hw.
  have hZero:L w=0:= (hK w).1 hw.
  rewrite inner_metric_distanceE.
  have h:=@orthogonal_projection_norm_bound R (R_n R n) (R_n R m)
    (@euclidean_inner_product R n) (@euclidean_inner_product R m) hN hM L
    (orthogonal_projection_map_projection p) (x-w).
  by rewrite linearB hZero subr0 in h.
- move=>x t hLower.
  have hKResidual:grassmann_val K (x-A (L x)).
    apply/(hK (x-A (L x))); exact:structure_projection_residual_kernel.
  have h:=hLower (x-A (L x)) hKResidual.
  by rewrite structure_projection_residual_distance in h.
Qed.

(** Source for [structure_projection_kernel_distance]: literal
    distance identity in Federer 3.3.1, p. 287, for every
    realization satisfying the original infimum definition. *)
Theorem structure_projection_kernel_distance (hmn:(m<=n)%N)
    (d:inner_metric_space hN->R):
  is_metric_set_distance [set x:inner_metric_space hN|grassmann_val (structure_projection_kernel hmn p) x] d ->
  forall x,d x=inner_norm hM (L x).
Proof.
move=>hd x.
have hp:=structure_projection_distance_laws (@structure_projection_kernelE R n m hmn p).
exact:(metric_set_distance_unique hd hp x).
Qed.
End ProjectionDistance.
