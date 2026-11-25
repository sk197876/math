(** Federer (1969), 3.4.3, p. 317: the vertical
    plane Z and admissibility of the convex open source S. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals topology.
From Federer Require Import Hom TensorUP ModuleQuotient GrassmannSubspaces GrassmannHomogeneousSpace
  GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct InnerNorm
  HilbertFormCompactness InnerConvex NormDifferentialUP NormRegularity NormRegularityOperations
  RealNormUP EuclideanBlockLinearMaps CoordinateProjection EuclideanProjectionSpace
  CriticalManifoldFamilyUP CriticalProjectionSectionFamily.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [critical_vertical_plane_exists]: the original
    Z={0} times R^(m-nu) in 3.4.3, p. 317.
    The standard last-block injection gives its actual Grassmann
    dimension and exact kernel equation. All witnesses are local. *)
Lemma critical_vertical_plane_exists (R:realType) nu l:
  exists Z:G (R_n R (nu+l)) l,forall x,
    grassmann_val Z x <->@euclidean_first_block R nu l x=0.
Proof.
pose J:=@euclidean_last_injection_map R nu l.
have hJ:injective (hom_as_linear J).
  move=>x y hEqual.
  have h:=congr1 (@euclidean_last_block R nu l) hEqual.
  by rewrite !euclidean_last_block_injectionK in h.
pose Z:=@linear_image_grassmann R (R_n R l) (R_n R (nu+l)) l
  (@coordinate_basis R l) (@coordinate_basisP R l) (hom_as_linear J) hJ.
exists Z;move=>x;rewrite linear_image_grassmannE;split.
- move=>[u <-];exact:euclidean_first_block_last_injection.
- move=>hx;exists (@euclidean_last_block R nu l x).
  have h:=@euclidean_block_linear_decomposition R nu l x.
  have hZero:@euclidean_first_injection R nu l 0=0.
    change (@euclidean_first_injection_map R nu l 0=0);exact:linear0.
  rewrite hx hZero add0r in h;exact:esym h.
Qed.

(** Source for [critical_open_manifold_family]: apply 3.4.2(9)
    with mu=m and the identity projection on the convex open
    S in 3.4.3, p. 317. Its kernel is zero
    and lies in every Z. The actual identity section proves
    admissibility; no submanifold assumption is added. *)
Theorem critical_open_manifold_family (R:realType) m d
    (Z:G (R_n R m) d) k (S:set (R_n R m)):
  (1<=k)%N ->is_inner_convex S ->
  (forall x,S x ->norm_domain_interior (inner_norm (@euclidean_inner_productP R m)) S x) ->
  critical_manifold_family Z m k S.
Proof.
move=>hk hConvex hOpen.
pose X:=R_n R m.
pose N:=inner_norm (@euclidean_inner_productP R m).
pose hN:=inner_norm_real_norm (@euclidean_inner_productP R m).
pose I:=@linear_id R X.
have hStar:O_star I by exists I;split;move=>x y.
have [p hP]:=euclidean_projection_linear_complete hStar.
have hBound:norm_bounded_linear N N (hom_of_linear I).
  exists 1;split;first exact:ler01.
  by move=>x;rewrite hom_of_linearE mul1r.
have hClass:=@norm_class_linear R X X N N hN hN S (hom_of_linear I) k hOpen hBound.
have hKernel x (hx:euclidean_projection_linear p x=0):grassmann_val Z x.
  have hX:x=0:=eq_trans (esym (hP x)) hx.
  rewrite hX;exact:subspace_zero.
have hFamily:=@critical_projection_section_family R m d Z m k p S (hom_of_linear I)
  (leq_subr d m) hk hKernel hConvex hClass (fun x _=>hP x).
have hImage:(hom_of_linear I @` S)=S.
  apply/seteqP;split;[by move=>x [u hu <-]|by move=>x hx;exists x].
by rewrite hImage in hFamily.
Qed.
