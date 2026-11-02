(** Federer (1969), 1.7.7, p. 34: choose an orthogonal injection whose image
    contains the factors of a simple vector. These existence statements
    expose no chosen construction. *)
From mathcomp Require Import all_boot all_order all_algebra boolp reals.
From Federer Require Import InnerProductUP OrthonormalFamilies OrthogonalMaps
  OrthogonalBasisCriteria BasisInterpolation LinearBasis FiniteCoordinates
  GrassmannAbbreviations EuclideanInnerProduct CoordinateProjection
  SimpleOrthonormalFactor AssociatedSubspace ExteriorGrading ExteriorMaps
  FiniteExteriorPowers ExteriorOperatorEstimate FrameImageSpan SimpleProducts
  SimpleElementary ModuleQuotient.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [orthonormal_frame_map_exists]: Federer 1.7.7,
    p. 34, supporting construction of an orthogonal map from R^m
    taking its standard basis to a prescribed orthonormal family. *)
Theorem orthonormal_frame_map_exists (R : realType) (V : lmodType R)
    (B : V -> V -> R) (hB : is_inner_product B)
    m (e : 'I_m -> V) (ho : orthonormal_family B e) :
  exists f : {linear R_n R m -> V},
    is_orthogonal_map (@euclidean_inner_product R m) B f /\
    forall i, f (@coordinate_basis R m i) = e i.
Proof.
pose f := basis_interpolation (@coordinate_basisP R m) e.
have hf i : f (@coordinate_basis R m i) = e i := basis_interpolationE _ _ _.
exists f; split; last exact hf.
apply: (@orthogonal_map_basis_criterion R (R_n R m) V
  (@euclidean_inner_product R m) B (@euclidean_inner_productP R m) hB
  m (@coordinate_basis R m) (@coordinate_basisP R m)).
- move=> i j; by rewrite euclidean_inner_basis /coordinate_basis ffunE eq_sym.
- move=> i j; by rewrite !hf ho.
Qed.

(** Source for [simple_orthogonal_frame_factor]: Federer 1.7.7,
    p. 34, a nonzero simple m-vector is in the image of the
    m-th exterior power of an orthogonal injection from R^m.
    This includes m=0 under the existing empty-product convention. *)
Theorem simple_orthogonal_frame_factor (R : realType)
    (h2 : (1+1 : R) != 0) (V : lmodType R)
    (B : V -> V -> R) (hB : is_inner_product B)
    m (x : exterior_power V m) (hx : x != 0) (sx : simple x) :
  exists (f : {linear R_n R m -> V}) (y : exterior_power (R_n R m) m),
    is_orthogonal_map (@euclidean_inner_product R m) B f /\
    exterior_power_map f m y = x.
Proof.
have [e [c [ho [hc hxe]]]] := @simple_orthonormal_factor R h2 V B hB m x hx sx.
have [f [hf hfe]] := orthonormal_frame_map_exists hB ho.
exists f, (c *: e_lambda (@coordinate_basis R m) (ord_tuple m)); split; first exact hf.
rewrite linearZ exterior_map_indexed_product.
have he : (fun i => f (@coordinate_basis R m i)) = e by apply: funext => i; exact: hfe.
rewrite he; exact: esym hxe.
Qed.

(** Source for [simple_orthogonal_frame_image]: Federer 1.7.7,
    p. 34, the orthogonal injection can be chosen with image exactly
    the subspace T associated with the nonzero simple vector. *)
Theorem simple_orthogonal_frame_image (R : realType)
    (h2 : (1+1 : R) != 0) (V : lmodType R)
    (B : V -> V -> R) (hB : is_inner_product B)
    m (x : exterior_power V m) (hx : x != 0) (sx : simple x) :
  exists f : {linear R_n R m -> V},
    is_orthogonal_map (@euclidean_inner_product R m) B f /\
    forall v, (exists u, f u = v) <-> FedererSimple.T x v.
Proof.
have [e [c [ho [hc hxe]]]] := @simple_orthonormal_factor R h2 V B hB m x hx sx.
have [f [hf hfe]] := orthonormal_frame_map_exists hB ho.
have he : e_lambda e (ord_tuple m) != 0.
  apply/eqP=> hz; move: hx; by rewrite hxe hz scaler0 eqxx.
exists f; split=> // v.
rewrite (@basis_image_finite_span R (R_n R m) V m
  (@coordinate_basis R m) (@coordinate_basisP R m) e f hfe v).
rewrite hxe (@associated_scale_nonzero R V m (e_lambda e (ord_tuple m)) c hc v).
symmetry; exact: (@product_associated_space R h2 V m e he v).
Qed.
