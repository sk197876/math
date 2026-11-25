(** Federer (1969), 3.3.10, p. 296: almost-everywhere
    transfer from original Grassmann planes to original projections. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets
  reals constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric FiniteCoordinates
  HomInner HomSpaceTopology GrassmannHomogeneousSpace EuclideanProjectionSpace
  StructureProjectionKernel StructureKernelProbability EuclideanGrassmannProbability
  OrthogonalProjectionProbability MeasurePushforward MeasureAlmostUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [structure_kernel_almost_transport]: the final
    theta-star almost-everywhere assertion of Federer 3.3.10,
    p. 296, using the exact original image-probability identity
    in 3.3.1, p. 287. Equality on every original subset transfers
    the actual exceptional set; no measurability or selected-plane
    hypothesis is added. *)
Theorem structure_kernel_almost_transport (R:realType) n m (hmn:(m<=n)%N)
    (P:set (grassmann_space (@euclidean_inner_productP R (n-m)) (@euclidean_inner_productP R n)
      (@coordinate_basisP R (n-m)) (@coordinate_basisP R n))):
  measure_almost_everywhere (@euclidean_grassmann_probability R n (n-m) (leq_subr m n)) P ->
  measure_almost_everywhere (@orthogonal_projection_probability R n m hmn)
    [set p:euclidean_projection_space R n m|P (structure_projection_kernel hmn p)].
Proof.
move=>hAlmost.
have hPush:=@structure_projection_kernel_probability R n m hmn.
have hValue:=congr1 (fun mu=>mu (~` P)) hPush.
exact:(eq_trans hValue hAlmost).
Qed.
