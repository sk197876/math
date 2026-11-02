(** Federer (1969), 3.2.35, p. 272:
    existence of the actual projection-fibre unit
    direction, reusing the proved orthogonal normal-line
    existence and exact adjoint laws. *)
From mathcomp Require Import all_boot all_order all_algebra reals topology.
From Federer Require Import Hom GrassmannAbbreviations EuclideanInnerProduct CoordinateProjection InnerProductUP InnerProductLaws
  OrthogonalMaps OrthogonalInjectionSpaces EuclideanProjectionSpace EuclideanProjectionMetric
  AdjointUP AdjointLaws EuclideanRectangularAdjoint EuclideanHyperplaneNormalUP EuclideanHyperplaneNormalExistence
  ProjectionLineNormalUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [projection_line_normal_exists]: supporting
    the line fibres of p in O*(n,n-1)
    in Federer 3.2.35, p. 272. Its
    actual adjoint injection has a proved unit
    normal and exact normal-line spanning law.
    Adjoint uniqueness identifies its projection with
    the original p. All auxiliary choices remain
    local, including the n=1, zero-target case. *)
Theorem projection_line_normal_exists (R:realType) k
    (p:orthogonal_projection_metric_space R k.+1 k):
  exists w,is_projection_line_normal p w.
Proof.
have hP:@is_orthogonal_projection R (R_n R k.+1) (R_n R k)
  (@euclidean_inner_product R k.+1) (@euclidean_inner_product R k) (euclidean_projection_linear p).
  exact:((O_star_projection (euclidean_projection_linear p)).1 (euclidean_projection_linear_member p)).
have [g [hOrthogonal hAdjoint]]:=hP.
pose alpha:=hom_of_linear g.
have hAlpha:is_orthogonal_map (@euclidean_inner_product R k)
    (@euclidean_inner_product R k.+1) (hom_as_linear alpha).
  exact hOrthogonal.
have hProjection z:euclidean_rectangular_adjoint alpha z=euclidean_projection_linear p z.
  apply:(inner_vectors_ext (@euclidean_inner_productP R k))=>x.
  rewrite euclidean_rectangular_adjoint_pairing.
  exact:esym (hAdjoint x z).
have [w hW]:=@euclidean_hyperplane_normal_exists R k alpha hAlpha.
exists w; constructor.
- exact:hyperplane_normal_unit hW.
- rewrite -hProjection; exact:hyperplane_normal_perpendicular hW.
- move=>z hz; apply:(hyperplane_normal_span hW).
  by rewrite hProjection.
Qed.
