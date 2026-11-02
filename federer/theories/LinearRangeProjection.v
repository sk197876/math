(** Federer (1969), 3.1.18, p. 229: choose p in O*(n,v) with
    image p*=image L, where L is the differential at the generic point.
    Only the finite rank of the image is required for existence. *)
From mathcomp Require Import all_boot all_order all_algebra boolp reals.
From Federer Require Import Hom ModuleQuotient SubspaceSums SubspaceCarrier
  InnerProductUP InnerProductLaws InnerProductRestriction InnerPolarity
  EuclideanInnerProduct GrassmannAbbreviations FiniteCoordinates
  OrthonormalFamilies OrthonormalisationUP GramSchmidt OrthonormalFrameMap
  OrthogonalMaps BasisInterpolation LinearBasis FiniteDualDimension Annihilator
  AdjointUP Adjoint AdjointLaws LinearRankUP.
From Federer Require Export LinearRangeProjectionUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [linear_range_projection_exists]: existence of the
    projection p selected in Federer 3.1.18, p. 229. An orthonormal
    basis of the actual range gives its orthogonal parametrisation;
    the already sealed adjoint gives p. No new project axiom is used. *)
Theorem linear_range_projection_exists (R:realType) (X Y:lmodType R)
    (C:Y->Y->R) (hC:is_inner_product C) (L:Hom X Y) v :
  has_linear_rank L v ->
  exists (p:{linear Y->R_n R v}) (j:{linear R_n R v->Y}),
    is_linear_range_projection C L p j.
Proof.
move=>[b hb].
pose W := range_subspace (hom_as_linear L).
pose CW := @restricted_inner_product R Y C W.
have hCW := @restricted_inner_productP R Y C hC W.
have [e [he hgs]] := @orthonormal_basis_exists R (subspace_space W) CW hCW v b hb.
have ho : orthonormal_family C (fun i=>subspace_val (e i)) := orthonormalisation_orthonormal hgs.
have [j [hj hje]] := orthonormal_frame_map_exists hC ho.
pose p := @inner_adjoint R (R_n R v) Y (@euclidean_inner_product R v) C
  (@euclidean_inner_productP R v) hC v (@coordinate_basis R v) (@coordinate_basisP R v) j.
have hp : is_adjoint (@euclidean_inner_product R v) C j p := inner_adjointP _ _ _ _.
exists p, j; constructor=>//.
- move=>u; apply: (inner_vectors_ext (@euclidean_inner_productP R v))=>z.
  by rewrite hp hj.
- move=>y; split.
  + move=>[u <-].
    have hu := congr1 j (basis_vector_expansion (@coordinate_basisP R v) u).
    rewrite linear_sum in hu.
    have hmem : W (j u).
      rewrite hu; elim/big_rec: _=>[|i z _ hz]; first exact: subspace_zero.
      apply: subspace_add=>//; rewrite linearZ hje.
      apply: subspace_scale; exact: subspace_valP.
    have [x hx] := hmem; exists x; exact: esym hx.
  + move=>[x hx].
    have hy : W y by exists x; exact: esym hx.
    pose u := subspace_lift hy.
    exists (\sum_i dual_basis he i u*: @coordinate_basis R v i).
    rewrite linear_sum.
    have h := congr1 subspace_val (basis_vector_expansion he u).
    rewrite subspace_liftE linear_sum in h.
    rewrite h; apply: eq_bigr=>i _.
    by rewrite !linearZ hje.
Qed.
