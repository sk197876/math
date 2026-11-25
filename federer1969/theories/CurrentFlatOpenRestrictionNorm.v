(** Federer (1969), 4.1.14, pp. 370–371: the
    actual flat norm at the original compact K is unchanged
    by restriction to any open neighbourhood of K. The two
    directions use exact zero extension and the preceding
    compact plateau representatives of original tests. *)
From mathcomp Require Import all_boot all_order all_algebra
  classical_sets reals constructive_ereal.
From Federer Require Import Hom RealNormUP NormDifferentialUP InnerNorm
  HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  CurrentSpaces SmoothCompactSet CurrentOpenRestriction CurrentLipschitzCompactImage
  CurrentFlatNorm CurrentFlatDualSeminormUP CurrentFlatDualSeminormSealed
  CurrentFlatOpenRestriction CurrentFlatTestNeighbourhood ExtendedSupremumUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [current_open_restriction_flat_norm]: the
    original F_K is identical on a current supported in K
    and its actual restriction to a source neighbourhood,
    supporting the representative law in 4.1.14,
    pp. 370–371. The compact carrier is exactly K;
    no normality, finite mass or representation is assumed. *)
Theorem current_open_restriction_flat_norm
    (R:realType) (h2:(1+1:R)!=0) n m (U Z:set (R_n R n))
    (hU:forall x,U x->norm_domain_interior
      (inner_norm (@euclidean_inner_productP R n)) U x)
    (hZ:forall x,Z x->norm_domain_interior
      (inner_norm (@euclidean_inner_productP R n)) Z x)
    (hZU:forall x,Z x->U x)
    (K:smooth_compact_set
      (inner_norm_real_norm (@euclidean_inner_productP R n)) U)
    (hKZ:smooth_compact_carrier K `<=` Z)
    (T:@current_space R h2 n U hU m):
  @current_support R h2 n U hU m T `<=` smooth_compact_carrier K->
  @current_flat_norm R h2 n m Z hZ
    (@current_compact_index_in_open R n U Z K hKZ)
    (@current_open_restriction R h2 n m Z U hZ hU hZU T)=
  @current_flat_norm R h2 n m U hU K T.
Proof.
move=>hSupport.
apply/eqP;rewrite eq_le;apply/andP;split.
- exact:(@current_open_restriction_flat_norm_le R h2 n m U Z hU hZ hZU K hKZ T).
- apply:(extended_supremum_least (@CurrentFlatDualSeminorm.laws R h2 n m
    U hU K (@current_value R h2 n U hU m T)))=>a [phi [hPhi hValue]].
  have[psi [hAction hBound]]:=@current_flat_test_neighbourhood_representative
    R h2 n m U Z hU hZ hZU K hKZ phi.
  apply:(extended_supremum_upper (@CurrentFlatDualSeminorm.laws R h2 n m
    Z hZ (@current_compact_index_in_open R n U Z K hKZ)
    (@current_value R h2 n Z hZ m
      (@current_open_restriction R h2 n m Z U hZ hU hZU T)))).
  exists psi;split;first exact:le_trans hBound hPhi.
  rewrite current_open_restriction_evaluation (hAction T hSupport).
  exact:hValue.
Qed.
