(** Federer (1969), 3.3.1, p. 287: p maps to ker p and takes
    theta*_(n,m) to gamma_(n,n-m). Both probabilities are specified
    independently. The existing 2.7.16(6) orbit-image laws and actual
    kernel equivariance prove the equality on every set. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets functions reals constructive_ereal topology.
From Federer Require Import Hom HomInner InnerMetric HomSpaceTopology GrassmannSubspaces
  GrassmannAbbreviations EuclideanInnerProduct
  FiniteCoordinates AdjointUP Adjoint OrthogonalGroupTopology
  OrthogonalInjectionSpaces EuclideanOrthogonalInvariantMeasures
  EuclideanProjectionSpace GrassmannHomogeneousSpace HomogeneousSpaceUP
  CompactGroupHaarNormalisation MeasurePushforward
  OrthogonalProjectionProbabilityUP OrthogonalProjectionProbability
  EuclideanGrassmannProbabilityUP EuclideanGrassmannProbability
  StructureProjectionKernel StructureKernelEquivariance.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [structure_projection_kernel_probability]: the
    last assertion of Federer 3.3.1, p. 287, with his actual
    independently specified probabilities: the image under the
    original kernel map equals gamma_(n,n-m). Haar witnesses and
    a base projection are local, and the equality holds on all
    subsets rather than requiring a supplied measurable-set premise. *)
Theorem structure_projection_kernel_probability (R:realType) n m
    (hmn:(m<=n)%N):
  @measure_pushforward R (euclidean_projection_space R n m)
    [the choiceType of grassmann_space
      (@euclidean_inner_productP R (n-m)) (@euclidean_inner_productP R n)
      (@coordinate_basisP R (n-m)) (@coordinate_basisP R n)]
    (@structure_projection_kernel R n m hmn)
    (@orthogonal_projection_probability R n m hmn)=
  @euclidean_grassmann_probability R n (n-m) (leq_subr m n).
Proof.
have [mulS [invS [eS hS]]]:=orthogonal_group_restriction_exists
  (@euclidean_inner_productP R n) (@coordinate_basisP R n).
have [theta [hLeft _ hTotal _]]:=euclidean_theta_exists_unique hS.
have hHaar:is_normalised_haar_measure mulS theta by split.
have [f hf]:=@euclidean_orthogonal_injection_exists R n m hmn.
have hp:is_orthogonal_projection (@euclidean_inner_product R n)
    (@euclidean_inner_product R m)
    (inner_adjoint (@euclidean_inner_productP R m)
      (@euclidean_inner_productP R n) (@coordinate_basisP R m) f).
  by exists f; split; [exact:hf|exact:inner_adjointP].
pose p0:=orthogonal_projection_of (@euclidean_inner_productP R m)
  (@euclidean_inner_productP R n) (@coordinate_basisP R n) hp.
have [eta [_ hUnique hOrbit]]:=euclidean_theta_star_nm_exists_unique hS hmn.
have hThetaStar:@orthogonal_projection_probability R n m hmn=
    measure_pushforward
      (orbit_map (orthogonal_projection_action (@euclidean_inner_productP R m)
        (@euclidean_inner_productP R n) (@coordinate_basisP R n) hS) p0) theta.
  rewrite (hUnique _ (orthogonal_projection_probability_specification hmn hS)).
  exact:esym (hOrbit theta p0 hHaar).
have [nu [_ hGammaUnique hGammaOrbit]]:=@euclidean_gamma_nm_exists_unique
  R n (n-m) mulS invS eS hS (leq_subr m n).
have hGamma:measure_pushforward
    (orbit_map (grassmann_action (@euclidean_inner_productP R (n-m))
      (@euclidean_inner_productP R n) (@coordinate_basisP R (n-m))
      (@coordinate_basisP R n)) (structure_projection_kernel hmn p0)) theta=
    @euclidean_grassmann_probability R n (n-m) (leq_subr m n).
  rewrite (hGammaUnique _ (@euclidean_grassmann_probability_specification R n (n-m) (leq_subr m n))).
  exact:(hGammaOrbit theta (structure_projection_kernel hmn p0) hHaar).
rewrite hThetaStar -hGamma /measure_pushforward.
apply:funext=>S; congr (theta _); apply:funext=>g; apply:propext.
change (S (structure_projection_kernel hmn
  (orthogonal_projection_action (@euclidean_inner_productP R m)
    (@euclidean_inner_productP R n) (@coordinate_basisP R n) hS g p0)) <->
  S (grassmann_action (@euclidean_inner_productP R (n-m))
    (@euclidean_inner_productP R n) (@coordinate_basisP R (n-m))
    (@coordinate_basisP R n) g (structure_projection_kernel hmn p0))).
by rewrite (structure_projection_kernel_equivariant hmn hS).
Qed.
