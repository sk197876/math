(** Federer (1969), 4.1.15, p. 373: an arbitrary affine
    d-plane is the image of an affine section of R^d into
    the ambient Euclidean space. The earlier orthogonal frame
    and adjoint laws supply this existence assertion; no new
    chosen parametrisation is exposed. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals topology.
From Federer Require Import Hom InnerProductUP InnerProductLaws InnerNorm
  GrassmannAbbreviations GrassmannSubspaces FiniteCoordinates EuclideanInnerProduct
  GrassmannHomogeneousSpace AffineMaps AffineSubspaceSpace AdjointUP Adjoint
  AdjointLaws OrthogonalMaps.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [affine_plane_lipschitz_section_exists]: supporting
    the arbitrary affine-plane assertion of Federer 4.1.15,
    p. 373. For every d-dimensional affine plane A there are
    affine f:R^d->R^n and g:R^n->R^d with g f=id and
    exact image A. Their regularity follows separately from
    the already proved finite-dimensional affine calculus. *)
Theorem affine_plane_lipschitz_section_exists (R : realType) n d
    (A : set (R_n R n))
    (hA : @is_affine_subspace_dim R (R_n R n) d A) :
  exists (f : R_n R d->R_n R n) (g : R_n R n->R_n R d),
    is_affine_map f /\ is_affine_map g /\
    (forall x,g (f x)=x) /\
    forall y,(exists x,f x=y)<->A y.
Proof.
have [a [W ->]]:=hA.
have [j [hOrthogonal hRange]]:=@grassmann_orthogonal_frame R
  (R_n R d) (R_n R n) (@euclidean_inner_product R d)
  (@euclidean_inner_product R n) (@euclidean_inner_productP R d)
  (@euclidean_inner_productP R n) d (@coordinate_basis R d)
  (@coordinate_basisP R d) W.
pose p:=@inner_adjoint R (R_n R d) (R_n R n)
  (@euclidean_inner_product R d) (@euclidean_inner_product R n)
  (@euclidean_inner_productP R d) (@euclidean_inner_productP R n)
  d (@coordinate_basis R d) (@coordinate_basisP R d) j.
have hAdjoint:is_adjoint (@euclidean_inner_product R d)
    (@euclidean_inner_product R n) j p.
  exact:inner_adjointP.
have hCancel:forall x,p (j x)=x.
  move=>x;apply:(inner_vectors_ext (@euclidean_inner_productP R d))=>z.
  by rewrite hAdjoint hOrthogonal.
pose f:=fun x:R_n R d=>a+j x.
pose g:=fun y:R_n R n=>-p a+p y.
have [hFAffine _ _ _]:=@affine_isomorphism R (R_n R d) (R_n R n) j a.
have [hGAffine _ _ _]:=@affine_isomorphism R (R_n R n) (R_n R d) p (-p a).
exists f,g;split;first exact:hFAffine.
split;first exact:hGAffine.
split.
- move=>x;by rewrite /g /f linearD addrA addNr add0r hCancel.
- move=>y;split.
  + move=>[x <-];apply:affine_coset_add.
    apply:(hRange (j x)).2;by exists x.
  + move=>hy.
    have [x hx]:=(hRange (y-a)).1 hy.
    exists x;by rewrite /f hx addrC subrK.
Qed.

Arguments affine_plane_lipschitz_section_exists : clear implicits.
