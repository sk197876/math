(** Federer (1969), 4.1.18, p. 377:
    zero extension transfers an original kernel
    pair to the whole space. The
    exact support law for open restriction
    detects zero when the original support
    lies in the smaller open domain. *)
From mathcomp Require Import all_boot all_order all_algebra
  classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormDifferentialUP InnerNorm
  HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  CurrentSpaces CurrentSupportGeometry CurrentSupportExtensionality
  CurrentOpenRestriction CurrentOpenRestrictionSupport.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [current_support_neighbourhood_restriction_zero]:
    a current supported in an open
    neighbourhood is zero when its original
    restriction there is zero, supporting the
    original-open kernel argument in Federer
    4.1.18, p. 377. This is
    a consequence of the exact restriction
    support law, with no mass or compactness premise. *)
Theorem current_support_neighbourhood_restriction_zero (R : realType)
    (h2 : (1+1:R)!=0) n m (U V : set (R_n R n))
    (hU : forall x, U x -> norm_domain_interior
      (inner_norm (@euclidean_inner_productP R n)) U x)
    (hV : forall x, V x -> norm_domain_interior
      (inner_norm (@euclidean_inner_productP R n)) V x)
    (hUV : U `<=` V) (T : @current_space R h2 n V hV m) :
  @current_support R h2 n V hV m T `<=` U ->
  @current_open_restriction R h2 n m U V hU hV hUV T=0 -> T=0.
Proof.
move=> hSupport hZero.
have hEmpty := (@current_empty_support_iff_zero R h2 n m U hU
  (@current_open_restriction R h2 n m U V hU hV hUV T)).2 hZero.
apply: (@current_empty_support_iff_zero R h2 n m V hV T).1=> x hx.
apply: (@hEmpty x).
rewrite current_open_restriction_support.
exact: (conj (@hSupport x hx) hx).
Qed.
