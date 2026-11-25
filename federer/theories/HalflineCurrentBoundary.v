(** Federer (1969), 4.1.7, p. 359:
    the original half-line current T has
    boundary delta_b on U=(0,infinity).
    Restrict the actual whole-line primitive;
    the excluded endpoint produces no extra
    point mass in the open domain. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import Hom RealNormUP NormDifferentialUP NormOpenDomainLaws
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct EuclideanOneCoordinate
  CurrentSpaces CurrentBoundary CurrentDirac CurrentDiracDensity CurrentOpenRestriction
  CurrentOpenRestrictionBoundary HalflineCurrents HalflinePrimitiveBoundary.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [halfline_current_boundary]: the
    actual equality boundary T=delta_b in
    D_0((0,infinity)), Federer 4.1.7,
    p. 359. The positive-b example
    follows; at excluded endpoints the actual
    restricted point current vanishes. *)
Theorem halfline_current_boundary (R:realType) (h2:(1+1:R)!=0) b:
  @current_boundary R h2 1 0%N (@current_halfline_domain R)
    (@current_halfline_domain_open R) (@halfline_current R h2 b)=
  @dirac_current R h2 1 (@current_halfline_domain R) (@current_halfline_domain_open R)
    (euclidean_one_embed b).
Proof.
rewrite /halfline_current -current_open_restriction_boundary halfline_left_primitive_boundary.
by [].
Qed.
