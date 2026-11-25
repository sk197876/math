(** Federer (1969), 4.1.14, pp. 371–372: on
    any open neighbourhood of spt T, the actual interval
    times the restricted compact flat current is flat.
    Localise the old compact index before restriction;
    no flat index equal to spt T is assumed. *)
From mathcomp Require Import all_boot all_order all_algebra
  classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  CurrentSpaces CurrentOpenRestriction CurrentHomotopyUP CurrentHomotopyDomain
  CurrentCartesianDomain CurrentCompactTimeCylinder CurrentFlatTimeCylinder
  CurrentLipschitzAffineChainUP CurrentFlatSupportNeighbourhoodRestriction
  CurrentLipschitzCompactImage FlatCurrentsUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [current_affine_neighbourhood_product_flat]: the
    actual product on a derived support neighbourhood belongs
    to the original compact flat space, supporting Federer
    4.1.14, pp. 371–372. Its compact index is proved
    to exist internally from original flat membership. *)
Theorem current_affine_neighbourhood_product_flat
    (R:realType) (h2:(1+1:R)!=0) n m
    (A:set R) (hA:@is_homotopy_parameter_interval R A)
    (U W:set (R_n R n))
    (hU:forall x,U x->norm_domain_interior
      (inner_norm (@euclidean_inner_productP R n)) U x)
    (hW:forall x,W x->norm_domain_interior
      (inner_norm (@euclidean_inner_productP R n)) W x)
    (hWU:forall x,W x->U x)
    (T:@current_space R h2 n U hU m)
    (hFlat:@is_flat_current R h2 n m U hU T)
    (hSupport:@current_support R h2 n U hU m T `<=` W) :
  @is_flat_current R h2 (1+n)%N (1+m)%N
    (@current_homotopy_product_domain R n A W)
    (@current_cartesian_domain_open R 1%N n (@current_homotopy_time_domain R A)
      W (@current_homotopy_time_domain_open R A hA) hW)
    (@current_affine_neighbourhood_product R h2 n m A hA U W hU hW hWU T).
Proof.
have [hRestricted _] := @flat_current_support_neighbourhood_restriction
  R h2 n m U W hU hW hWU T hFlat hSupport.
have [K hK] := hRestricted.
exists (@current_compact_time_cylinder R n A W hA K).
exact: (@flat_current_time_cylinder R h2 n m A W hA hW K
  (@current_open_restriction R h2 n m W U hW hU hWU T) hK).
Qed.
