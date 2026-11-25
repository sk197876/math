(** Federer (1969), 4.1.26, p. 384:
    boundary(E^m restricted to A) is supported
    in Clos A intersect Clos(R^m minus A).
    The proof follows the displayed complementary
    restriction identity and boundary locality. There
    is no finite-perimeter or smooth-boundary premise. *)
From mathcomp Require Import all_boot all_order all_algebra
  classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP NormOpenDomainLaws
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  CurrentSpaces CurrentBoundary CurrentBoundarySupport CurrentSupportLinearUnion
  CurrentSupportExtensionality EuclideanFundamentalCurrent EuclideanCharacteristicCurrent
  EuclideanLebesgueDimensions MeasureUP MeasureFiniteClosure
  CurrentCharacteristicComplement CurrentCharacteristicSupportClosure.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section CurrentCharacteristicBoundarySupport.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variable p:nat.
Local Notation X:=(R_n R p.+1).
Local Notation N:=(inner_norm (@euclidean_inner_productP R p.+1)).
Local Notation hN:=(inner_norm_real_norm (@euclidean_inner_productP R p.+1)).
Local Notation XT:=(real_norm_metric_space hN).
Local Notation U:=(fun _:X=>True).
Local Notation hU:=(fun (x:X) (_:True)=>norm_full_domain_interior N x).
Variable A:set X.
Hypothesis hA:measure_measurable (@euclidean_lebesgue_measure R p.+1) A.
Let hAc:=@measure_measurable_complement R X (@euclidean_lebesgue_measure R p.+1) A hA.
Local Notation TA:=(@euclidean_characteristic_current R h2 p.+1 A hA).
Local Notation TC:=(@euclidean_characteristic_current R h2 p.+1 (~` A) hAc).
Local Notation bd:=(@current_boundary R h2 p.+1 p U hU).

(** Source for [euclidean_characteristic_boundary_complement]:
    the first displayed boundary identity of
    4.1.26, p. 384: the complementary restricted
    Euclidean currents have opposite boundaries. *)
Theorem euclidean_characteristic_boundary_complement:bd TA= -bd TC.
Proof.
have hSum:=congr1 bd (@euclidean_characteristic_current_complement_sum
  R h2 p.+1 A hA hAc).
rewrite linearD euclidean_fundamental_current_boundary_zero in hSum.
have h:=congr1 (fun T=>T-bd TC) hSum.
by rewrite addrK sub0r in h.
Qed.

(** Source for [euclidean_characteristic_boundary_support]:
    spt boundary(E^m restricted to A) is
    contained in Bdry A, expressed by the
    literal intersection of the two closures,
    Federer 4.1.26, p. 384. Boundedness is
    unnecessary for this supporting inclusion. *)
Theorem euclidean_characteristic_boundary_support:
  @current_support R h2 p.+1 U hU p (bd TA) `<=`
    (@closure XT A `&` @closure XT (~` A)).
Proof.
move=>x hx;split.
- apply:(@euclidean_characteristic_current_support_closure R h2 p.+1 A hA x).
  exact:(@current_boundary_support_subset R h2 p.+1 p U hU TA x hx).
- have hNegativeSupport:@current_support R h2 p.+1 U hU p (-bd TC) x.
    by rewrite -euclidean_characteristic_boundary_complement.
  have hUnion:=@current_support_linear_union R h2 p.+1 p U hU (-1) (bd TC) 0.
  rewrite scaleN1r addr0 in hUnion.
  have hTC:@current_support R h2 p.+1 U hU p (bd TC) x.
    case:(hUnion x hNegativeSupport)=>[h|h];first exact:h.
    have hEmpty:=(@current_empty_support_iff_zero R h2 p.+1 p U hU 0).2 (erefl _).
    exact:False_ind _ (hEmpty x h).
  apply:(@euclidean_characteristic_current_support_closure R h2 p.+1 (~` A) hAc x).
  exact:(@current_boundary_support_subset R h2 p.+1 p U hU TC x hTC).
Qed.
End CurrentCharacteristicBoundarySupport.
