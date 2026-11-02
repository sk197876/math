(** Federer (1969), 1.7.7, p. 34: the nonzero simple-vector projection
    supremum is attained by the adjoint of an orthogonal frame. The ambient
    inner-product space may be arbitrary-dimensional; only the frame source
    is finite. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import InnerProductUP InnerNorm AdjointUP Adjoint
  OrthogonalMaps AdjointCriteria ExteriorGrading ExteriorMaps ExteriorNorm
  ExteriorProjectionNorm OrthonormalFrameMap AssociatedSubspace
  EuclideanInnerProduct GrassmannAbbreviations FiniteCoordinates CoordinateProjection.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [simple_projection_norm_attained]: Federer 1.7.7,
    p. 34, choose an orthogonal injection from R^m and its adjoint
    projection so that projecting the given nonzero simple m-vector
    preserves its norm. *)
Theorem simple_projection_norm_attained (R : realType)
    (h2 : (1+1 : R) != 0) (V : lmodType R)
    (B : V -> V -> R) (hB : is_inner_product B)
    m (x : exterior_power V m) (hx : x != 0) (sx : simple x) :
  exists (f : {linear R_n R m -> V}) (p : {linear V -> R_n R m}),
    is_orthogonal_map (@euclidean_inner_product R m) B f /\
    is_adjoint (@euclidean_inner_product R m) B f p /\
    exterior_norm h2 (@euclidean_inner_productP R m) (exterior_power_map p m x) =
      exterior_norm h2 hB x.
Proof.
have [f [y [hf hy]]] := simple_orthogonal_frame_factor h2 hB hx sx.
pose p := inner_adjoint (@euclidean_inner_productP R m) hB (@coordinate_basisP R m) f.
have ha : is_adjoint (@euclidean_inner_product R m) B f p := inner_adjointP _ _ _ _.
exists f, p; split=> //; split=> //.
rewrite -hy (@exterior_adjoint_retraction R (R_n R m) V
  (@euclidean_inner_product R m) B (@euclidean_inner_productP R m) f p ha hf m).
symmetry; exact: exterior_orthogonal_norm.
Qed.
