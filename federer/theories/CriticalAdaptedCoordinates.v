(** Federer (1969), 3.4.2(8), p. 315: orthonormal
    coordinates adapted to the actual subspace p(Z). *)
From mathcomp Require Import all_boot all_order all_algebra reals topology.
From Federer Require Import Hom ModuleQuotient SubspaceCarrier GrassmannSubspaces
  GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct InnerProductUP
  InnerProductRestriction LinearBasis FiniteBasisComparison GramSchmidt
  OrthonormalFamilies OrthonormalisationUP OrthonormalCapacityExtension
  OrthogonalMaps OrthonormalFrameMap CoordinateProjection EuclideanCoordinateTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [critical_adapted_coordinates_exists]: the
    perpendicular coordinate split for the cubes A and B in
    3.4.2(8), p. 315. Extend an actual orthonormal basis of
    p(Z) to the whole target space. Vectors supported in its
    first a coordinates map into p(Z), including a=0. *)
Theorem critical_adapted_coordinates_exists (R:realType) mu a
    (A:G (R_n R mu) a) (hA:(a<=mu)%N):
  exists H:{linear R_n R mu->R_n R mu},
    is_orthogonal_map (@euclidean_inner_product R mu)
      (@euclidean_inner_product R mu) H /\
    forall x:R_n R mu,(forall i:'I_mu,(a<=i)%N ->x i=0) ->grassmann_val A (H x).
Proof.
have [b hb]:=grassmann_proof A.
have [e [he hGS]]:=@orthonormal_basis_exists R
  (subspace_space (grassmann_val A)) _
  (restricted_inner_productP (@euclidean_inner_productP R mu) (grassmann_val A)) a b hb.
pose v i:=subspace_val (e i).
have hV:orthonormal_family (@euclidean_inner_product R mu) v:=
  orthonormalisation_orthonormal hGS.
have [d [hD hInitial]]:=@orthonormal_capacity_extension R (R_n R mu)
  (@euclidean_inner_product R mu) (@euclidean_inner_productP R mu)
  mu (@coordinate_basis R mu) (finite_basis_independent (@coordinate_basisP R mu))
  a v hV hA.
have [H [hH hBasis]]:=orthonormal_frame_map_exists (@euclidean_inner_productP R mu) hD.
exists H;split;first exact:hH.
move=>x hSupport.
have hExpansion:H x=\sum_(i<mu) x i *:d i.
  rewrite -{1}(euclidean_coordinate_expansion x) linear_sum.
  apply:eq_bigr=>i _;by rewrite linearZ hBasis.
rewrite hExpansion;apply:(big_ind (fun z=>grassmann_val A z)).
- exact:subspace_zero.
- exact:subspace_add.
- move=>i _;case:(ltnP i a)=>hi.
  + have hIndex:i=widen_ord hA (Ordinal hi) by apply:val_inj.
    rewrite hIndex hInitial;apply:subspace_scale;exact:subspace_valP.
  + by rewrite (hSupport i hi) scale0r;exact:subspace_zero.
Qed.
