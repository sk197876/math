(** Federer (1969), 3.3.18, p. 301: the original approximate
    normal of an m-dimensional tangent is the actual perpendicular plane. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations GrassmannSubspaces ModuleQuotient
  EuclideanInnerProduct InnerNorm InnerMetric HilbertFormCompactness FiniteCoordinates
  GrassmannHomogeneousSpace CoordinateProjection EuclideanProjectionSpace StructureProjectionKernel
  Adjoint AdjointUP InnerProductUP InnerProductLaws Bilinear BilinearNegation
  RectifiableTangentPlaneUP MeasureApproximateTangentUP MeasureApproximateNormalUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [approximate_tangent_normal_plane_exists]: the original
    normal plane in the final assertion of Federer 3.3.18, p. 301.
    An actual orthogonal frame of the original tangent and its sealed
    adjoint give a projection whose actual kernel equals the polar
    normal. Both nonpositive polar inequalities force equality on
    the tangent subspace. The original normal has dimension n-m;
    no frame, projection or normal plane is an extra theorem premise. *)
Theorem approximate_tangent_normal_plane_exists (R:realType) n m (hmn:(m<=n)%N)
    (mu:set (R_n R n)->\bar R) (a:R_n R n):
  is_m_dimensional_approximate_tangent m mu a ->
  exists N:G (R_n R n) (n-m),forall u,
    grassmann_val N u <->measure_approximate_normal_cone (@euclidean_inner_productP R n) mu m a u.
Proof.
move=>[T hT].
have [f [hf hRange]]:=@grassmann_orthogonal_frame R (R_n R m) (R_n R n)
  (@euclidean_inner_product R m) (@euclidean_inner_product R n)
  (@euclidean_inner_productP R m) (@euclidean_inner_productP R n)
  m (@coordinate_basis R m) (@coordinate_basisP R m) T.
pose g:=@inner_adjoint R (R_n R m) (R_n R n)
  (@euclidean_inner_product R m) (@euclidean_inner_product R n)
  (@euclidean_inner_productP R m) (@euclidean_inner_productP R n)
  m (@coordinate_basis R m) (@coordinate_basisP R m) f.
have hg:is_adjoint (@euclidean_inner_product R m) (@euclidean_inner_product R n) f g:=
  @inner_adjointP R (R_n R m) (R_n R n)
    (@euclidean_inner_product R m) (@euclidean_inner_product R n)
    (@euclidean_inner_productP R m) (@euclidean_inner_productP R n)
    m (@coordinate_basis R m) (@coordinate_basisP R m) f.
have hp:O_star g by exists f.
have [p hEval]:=euclidean_projection_linear_complete hp.
exists (structure_projection_kernel hmn p)=>u.
rewrite structure_projection_kernelE hEval.
have hNormal:measure_approximate_normal_cone (@euclidean_inner_productP R n) mu m a u <->
    forall v,grassmann_val T v ->@euclidean_inner_product R n u v= 0.
  rewrite /measure_approximate_normal_cone hT; split.
  - move=>h v hv.
    have hPos:=h v hv.
    have hOpp:grassmann_val T (-v).
      rewrite -scaleN1r; exact:subspace_scale _ hv.
    have hNeg:=h (-v) hOpp.
    rewrite (bilNr (@euclidean_inner_bilinear R n)) oppr_le0 in hNeg.
    apply/eqP; by rewrite eq_le hPos hNeg.
  - move=>h v hv; by rewrite h.
rewrite hNormal; split.
- move=>hZero v /hRange [x <-].
  rewrite (inner_symmetric (@euclidean_inner_productP R n)) -hg hZero.
  exact:(bil0r (@euclidean_inner_bilinear R m) x).
- move=>h.
  apply/eqP; rewrite -(inner_self_eq0 (@euclidean_inner_productP R m)).
  apply/eqP; rewrite hg (inner_symmetric (@euclidean_inner_productP R n)).
  apply:h; apply/hRange; by exists (g u).
Qed.
