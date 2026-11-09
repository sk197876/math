(** Federer (1969), 3.4.2(8), p. 315: the projection is
    isometric on the perpendicular complement of its actual kernel. *)
From mathcomp Require Import all_boot all_order all_algebra reals topology.
From Federer Require Import Bilinear Hom ModuleQuotient GrassmannSubspaces GrassmannAbbreviations
  FiniteCoordinates EuclideanInnerProduct InnerProductUP InnerProductLaws InnerNorm
  OrthogonalComplement EuclideanProjectionSpace OrthogonalInjectionSpaces
  EuclideanRectangularAdjoint StructureProjectionKernel StructureProjectionDistance
  LinearRankUP FiniteSourceLinearRank.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [critical_projection_adjoint]: the original adjoint
    injection in the orthogonal splitting used in 3.4.2(8),
    p. 315, already specified and sealed in 1.7.4. This type
    adapter fixes the geometry parameters; it selects no new map. *)
Definition critical_projection_adjoint (R:realType) m mu
    (p:euclidean_projection_space R m mu):Hom (R_n R mu) (R_n R m):=
  @euclidean_rectangular_adjoint R m mu
    (@orthogonal_projection_map R (R_n R mu) (R_n R m)
      (@euclidean_inner_product R mu) (@euclidean_inner_product R m)
      (@euclidean_inner_productP R mu) (@euclidean_inner_productP R m)
      m (@coordinate_basis R m) (@coordinate_basisP R m) p).

(** Source for [critical_projection_adjoint_cancel]: the adjoint
    section identity p p*=id from 1.7.4, supporting the dimension
    and isometry calculations of 3.4.2(8), p. 315. *)
Lemma critical_projection_adjoint_cancel (R:realType) m mu
    (p:euclidean_projection_space R m mu):
  cancel (critical_projection_adjoint p) (euclidean_projection_linear p).
Proof. move=>u;exact:(@structure_projection_adjoint_cancel R m mu p u). Qed.

(** Source for [critical_projection_dimension_bound]: the original
    projection in 3.4.2(3), p. 310, has target dimension at most
    m. Its actual injective adjoint and the basis-size theorem
    prove the bound needed in the split of (8), p. 315. *)
Lemma critical_projection_dimension_bound (R:realType) m mu
    (p:euclidean_projection_space R m mu):(mu<=m)%N.
Proof.
pose J:=critical_projection_adjoint p.
have hInjective:injective J.
  move=>x y hEqual.
  have hh:=congr1 (euclidean_projection_linear p) hEqual.
  by rewrite !critical_projection_adjoint_cancel in hh.
have hRank:=@finite_source_injective_linear_rank R (R_n R mu) (R_n R m)
  J mu (@coordinate_basis R mu) (@coordinate_basisP R mu) hInjective.
exact:(@linear_rank_codomain_bound R (R_n R mu) (R_n R m) J m
  (@coordinate_basis R m) (@coordinate_basisP R m) mu hRank).
Qed.

(** Source for [critical_projection_perpendicular_fixed]: the
    isometric inverse on (ker p) perpendicular, supporting the
    dimension split in 3.4.2(8), p. 315. The residual x-p*p(x)
    lies in ker p. Both x and p*p(x) are perpendicular to that
    residual, so positive definiteness forces it to be zero. *)
Theorem critical_projection_perpendicular_fixed (R:realType) m mu (hMu:(mu<=m)%N)
    (p:euclidean_projection_space R m mu) x:
  orthogonal_complement (@euclidean_inner_productP R m)
    (grassmann_val (structure_projection_kernel hMu p)) x ->
  x=critical_projection_adjoint p (euclidean_projection_linear p x).
Proof.
move=>hPerp.
pose B:=@euclidean_inner_product R m.
pose hB:=@euclidean_inner_productP R m.
pose P:=euclidean_projection_linear p.
pose J:=critical_projection_adjoint p.
pose v:=x-J (P x).
have hKernel:P v=0:=@structure_projection_residual_kernel R m mu p x.
have hMember:grassmann_val (structure_projection_kernel hMu p) v:=
  (structure_projection_kernelE hMu p v).2 hKernel.
have hFirst:B x v=0:=hPerp v hMember.
have hSecond:B (J (P x)) v=0.
  have hh:=@structure_projection_adjointE R m mu p (P x) v.
  rewrite hKernel (bil0r (inner_bilinear (@euclidean_inner_productP R mu))) in hh.
  exact:esym hh.
have hSelf:B v v=0.
  have hDifference:B v v=B x v-B (J (P x)) v:=
    bilBl (inner_bilinear hB) x (J (P x)) v.
  by rewrite hFirst hSecond subrr in hDifference.
have hZero:v=0.
  have hEquiv:((B v v==0)=(v==0)):=inner_self_eq0 hB v.
  apply/eqP;rewrite -hEquiv;apply/eqP;exact:hSelf.
by apply/eqP;rewrite -subr_eq0;apply/eqP;exact:hZero.
Qed.

(** Source for [critical_projection_perpendicular_inner]: the
    projection preserves inner products on the kernel complement,
    supporting the orthonormal coordinates in 3.4.2(8), p. 315. *)
Lemma critical_projection_perpendicular_inner (R:realType) m mu (hMu:(mu<=m)%N)
    (p:euclidean_projection_space R m mu) x y:
  orthogonal_complement (@euclidean_inner_productP R m)
    (grassmann_val (structure_projection_kernel hMu p)) x ->
  orthogonal_complement (@euclidean_inner_productP R m)
    (grassmann_val (structure_projection_kernel hMu p)) y ->
  euclidean_inner_product (euclidean_projection_linear p x) (euclidean_projection_linear p y)=
    euclidean_inner_product x y.
Proof.
move=>hx hy.
have hX:=@critical_projection_perpendicular_fixed R m mu hMu p x hx.
have hY:=@critical_projection_perpendicular_fixed R m mu hMu p y hy.
have hh:=@structure_projection_adjoint_orthogonal R m mu p
  (euclidean_projection_linear p x) (euclidean_projection_linear p y).
rewrite -hX -hY in hh;exact:esym hh.
Qed.
