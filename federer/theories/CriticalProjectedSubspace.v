(** Federer (1969), 3.4.2(8), p. 315: the actual subspace
    p(Z) has dimension mu-nu, where nu=m-dim(Z). *)
From mathcomp Require Import all_boot all_order all_algebra reals topology.
From Federer Require Import Hom ModuleQuotient SubspaceCarrier SubspaceSums TensorUP
  GrassmannSubspaces GrassmannAbbreviations FiniteCoordinates LinearBasis
  EuclideanInnerProduct EuclideanProjectionSpace StructureProjectionKernel
  OrthogonalComplement LinearRangeBasis CriticalOrthogonalRemainder
  CriticalProjectionPerpendicular.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [critical_projected_subspace_exists]: the dimension
    mu-nu of p(Z), used to choose A in 3.4.2(8), p. 315.
    Split Z by the actual kernel. The projection is injective
    on its perpendicular remainder; mapped bases give its image
    dimension. All choices remain local to this existence proof. *)
Theorem critical_projected_subspace_exists (R:realType) m d mu
    (Z:G (R_n R m) d) (p:euclidean_projection_space R m mu)
    (hD:(d<=m)%N):
  (forall x,euclidean_projection_linear p x=0 ->grassmann_val Z x) ->
  exists A:G (R_n R mu) (mu-(m-d)),forall y,
    grassmann_val A y <->exists x,grassmann_val Z x /\
      euclidean_projection_linear p x=y.
Proof.
move=>hKernel.
have hMu:=critical_projection_dimension_bound p.
pose K:=structure_projection_kernel hMu p.
have hKZ x:grassmann_val K x ->grassmann_val Z x.
  move=>hx;apply:hKernel;exact:(structure_projection_kernelE hMu p x).1 hx.
have [W [hW hSplit]]:=@critical_orthogonal_remainder_exists R (R_n R m)
  (@euclidean_inner_product R m) (@euclidean_inner_productP R m)
  m (@coordinate_basis R m) (@coordinate_basisP R m) d (m-mu) Z K hKZ.
pose F:=linear_comp (euclidean_projection_linear p)
  (@subspace_inclusion R (R_n R m) (grassmann_val W)).
have hInjective:injective F.
  move=>x y hEqual;apply:subspace_val_injective.
  have hx:orthogonal_complement (@euclidean_inner_productP R m)
    (grassmann_val K) (subspace_val x):=((hW _).1 (subspace_valP x)).2.
  have hy:orthogonal_complement (@euclidean_inner_productP R m)
    (grassmann_val K) (subspace_val y):=((hW _).1 (subspace_valP y)).2.
  have hX:=@critical_projection_perpendicular_fixed R m mu hMu p (subspace_val x) hx.
  have hY:=@critical_projection_perpendicular_fixed R m mu hMu p (subspace_val y) hy.
  rewrite hX hY;apply:congr1;exact:hEqual.
have [b hb]:=grassmann_proof W.
have [a ha]:=injective_range_basis_exists hInjective hb.
have hDim:(d-(m-mu)=mu-(m-d))%N.
  rewrite (@subnBA d m mu hMu) (@subnBA mu m d hD) addnC;reflexivity.
have hRange y:range_subspace F y <->exists x,grassmann_val Z x /\
    euclidean_projection_linear p x=y.
  split.
  - move=>[w hEqual];exists (subspace_val w);split.
    + exact:((hW _).1 (subspace_valP w)).1.
    + exact:esym hEqual.
  - move=>[x [hx <-]].
    have [u [w [hu [hw hEq]]]]:=(hSplit x).1 hx.
    exists (subspace_lift hw).
    change (euclidean_projection_linear p x=euclidean_projection_linear p w).
    rewrite hEq (linearD (euclidean_projection_linear p)).
    by rewrite ((structure_projection_kernelE hMu p u).1 hu) add0r.
rewrite -hDim;exists (@GrassmannSubspace R (R_n R mu) (d-(m-mu))
  (range_subspace F) (ex_intro _ a ha));exact:hRange.
Qed.
