(** Federer (1969), 4.1.27, p. 384:
    the displayed cube map is smooth on
    its whole Euclidean source. Reuse the
    existing bounded coordinate maps, finite sums
    and scalar-product class laws of 3.1.11.
    Smoothness does not assert a global
    Lipschitz bound for the polynomial itself. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals.
From Federer Require Import Hom RealNormUP NormDifferentialUP NormOpenDomainLaws
  NormRegularity NormRegularityOperations NormRegularityBilinear
  NormRegularityFiniteSum InnerNorm HilbertFormCompactness
  GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct
  EuclideanScalarCoordinateMaps SimplexCubeParametrisationUP
  SimplexCubeParametrisationSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [simplex_cube_prefix_class]: the finite
    products x_1 ... x_k in the
    original map of 4.1.27, p. 384,
    have every finite differentiability class, by
    the preceding product calculus. *)
Theorem simplex_cube_prefix_class (R:realType) m k q:
  norm_class (inner_norm_real_norm (@euclidean_inner_productP R m))
    (@scalar_absolute_value_norm R) (fun _=>True)
    (fun x:R_n R m=>simplex_cube_prefix_product x k) q.
Proof.
pose X:=R_n R m.
pose N:=inner_norm (@euclidean_inner_productP R m).
pose hN:=inner_norm_real_norm (@euclidean_inner_productP R m).
pose hR:=@scalar_absolute_value_norm R.
pose Full:=fun _:X=>True.
pose hFull:=fun (x:X) (_:True)=>norm_full_domain_interior N x.
have hOne:norm_class hN hR Full (fun _:X=>(1:R^o)) q.
  exact:(@norm_class_constant R X R^o N (fun t:R^o=>`|t|) hN hR Full 1 q hFull).
have hEach i:norm_class hN hR Full (fun x:X=>(x i:R^o)) q.
  exact:(@norm_class_linear R X R^o N (fun t:R^o=>`|t|) hN hR Full
    (@euclidean_scalar_coordinate_map R m i) q hFull
    (@euclidean_scalar_coordinate_bounded R m i)).
have hSequence (s:seq 'I_m):norm_class hN hR Full
    (fun x:X=>(\prod_(i<-s | (i<k)%N) x i:R^o)) q.
  elim:s=>[|i s hS].
  - apply:(norm_class_domain_agreement _ hOne)=>x _;by rewrite big_nil.
  - case hI:(i<k)%N.
    + apply:(norm_class_domain_agreement _ (norm_class_scalar_product (hEach i) hS))=>x _.
      by rewrite big_cons hI.
    + apply:(norm_class_domain_agreement _ hS)=>x _.
      by rewrite big_cons hI.
exact:hSequence (index_enum 'I_m).
Qed.

(** Source for [simplex_cube_parametrisation_smooth]: the original
    f in 4.1.27, p. 384, is
    of class infinity on R^m for
    arbitrary vertices. Repeated and affinely dependent
    vertices require no separate analytic hypothesis. *)
Theorem simplex_cube_parametrisation_smooth (R:realType) n m
    (v:'I_(m.+1)->R_n R n):
  norm_class_all_orders (inner_norm_real_norm (@euclidean_inner_productP R m))
    (inner_norm_real_norm (@euclidean_inner_productP R n))
    (fun _=>True) (@SimplexCubeParametrisation.value R n m v).
Proof.
pose X:=R_n R m;pose Y:=R_n R n.
pose NX:=inner_norm (@euclidean_inner_productP R m).
pose NY:=inner_norm (@euclidean_inner_productP R n).
pose hNX:=inner_norm_real_norm (@euclidean_inner_productP R m).
pose hNY:=inner_norm_real_norm (@euclidean_inner_productP R n).
pose Full:=fun _:X=>True.
pose hFull:=fun (x:X) (_:True)=>norm_full_domain_interior NX x.
move=>q.
have hBase:=@norm_class_constant R X Y NX NY hNX hNY Full (v ord0) q hFull.
have hTerm i:norm_class hNX hNY Full
    (fun x:X=>simplex_cube_prefix_product x (val i).+1*:
      simplex_consecutive_edge_family v i) q.
  have hEdge:=@norm_class_constant R X Y NX NY hNX hNY Full
    (simplex_consecutive_edge_family v i) q hFull.
  exact:norm_class_scalar_product (@simplex_cube_prefix_class R m (val i).+1 q) hEdge.
have hSum:=@norm_class_finite_sum R X Y NX NY hNX hNY Full
  (Finite.clone 'I_m _) (fun i x=>simplex_cube_prefix_product x (val i).+1*:
    simplex_consecutive_edge_family v i) q hFull hTerm.
apply:(norm_class_domain_agreement _ (norm_class_add hBase hSum))=>x _.
exact:esym (SimplexCubeParametrisation.laws R n m v x).
Qed.
