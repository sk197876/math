(** Federer (1969), 4.1.12, p. 369: the
    second Cartesian flat estimate has the exact
    binomial(i+j+2,i+1) coefficient. The proof uses
    the actual separated tests and their two original
    suprema, with every current and both zero degrees. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal.
From Federer Require Import Hom RealNormUP NormDifferentialUP InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct EuclideanCartesianMap CurrentSpaces
  SmoothCompactSet CurrentCartesianDomain CurrentCartesianProductUP CurrentCartesianProductSealed
  CurrentCartesianTestProductSealed CurrentCartesianFlatTestBound CurrentFlatNorm
  CurrentFlatFormSeminormLaws CurrentFlatDualSeminormUP CurrentFlatDualSeminormSealed
  CurrentFlatDualSeminormBasic ExtendedSupremumProductBound.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section CurrentFlatCartesianLower.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables m n i j:nat.
Local Notation NX := (inner_norm (@euclidean_inner_productP R m)).
Local Notation NY := (inner_norm (@euclidean_inner_productP R n)).
Local Notation hNX := (inner_norm_real_norm (@euclidean_inner_productP R m)).
Local Notation hNY := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation hNZ := (inner_norm_real_norm (@euclidean_inner_productP R (m+n))).
Variables (A:set (R_n R m)) (B:set (R_n R n)).
Hypothesis hA:forall a,A a->norm_domain_interior NX A a.
Hypothesis hB:forall b,B b->norm_domain_interior NY B b.
Local Notation AB := (@euclidean_cartesian_set R m n A B).
Local Notation hAB := (@current_cartesian_domain_open R m n A B hA hB).
Variables (KA:smooth_compact_set hNX A) (KB:smooth_compact_set hNY B)
  (KAB:smooth_compact_set hNZ AB).
Hypothesis hKAB:smooth_compact_carrier KAB=
  @euclidean_cartesian_set R m n (smooth_compact_carrier KA) (smooth_compact_carrier KB).
Local Notation CA := (@current_space R h2 m A hA i).
Local Notation CB := (@current_space R h2 n B hB j).
Local Notation ea := (@current_value R h2 m A hA i).
Local Notation eb := (@current_value R h2 n B hB j).
Local Notation ec := (@current_value R h2 (m+n) AB hAB (i+j)).
Local Notation FA := (@current_flat_test_seminorm R h2 m i A hA KA).
Local Notation FB := (@current_flat_test_seminorm R h2 n j B hB KB).
Local Notation FC := (@current_flat_test_seminorm R h2 (m+n) (i+j) AB hAB KAB).
Local Notation FK := (@current_flat_norm R h2 m i A hA KA).
Local Notation FL := (@current_flat_norm R h2 n j B hB KB).
Local Notation FM := (@current_flat_norm R h2 (m+n) (i+j) AB hAB KAB).
Local Notation Pure := (@CartesianTestProduct.value R h2 m n A B hA hB i j).
Local Notation Product := (@CartesianCurrentProduct.value R h2 m n i j A B hA hB).

(** Source for [current_flat_cartesian_lower]:
    F_C(S) F_D(T) is at most
    binomial(i+j+2,i+1) F_(C times D)(S times T),
    the second printed inequality in Federer
    4.1.12, p. 369. No support, representation
    or finiteness assumption is added. The original
    ordinary partial-product domain is explicit. *)
Theorem current_flat_cartesian_lower (S:CA) (T:CB):
  mule_def (FK S) (FL T)->
  (FK S * FL T<='C((i+j).+2,i.+1)%:R%:E * FM (Product S T))%E.
Proof.
move=>hDef;pose c:R:='C((i+j).+2,i.+1)%:R.
have hIndex:(i.+1<=(i+j).+2)%N.
  have h:=leq_trans (leq_addr j i) (leqnSn (i+j));exact:h.
have hc:0<c by rewrite /c ltr0n bin_gt0.
case:(ltP (FM (Product S T)) (+oo)%E)=>hFinite.
- have [a [ha hValue]]:=@current_flat_dual_finite_value R h2 (m+n) (i+j) AB hAB KAB
    (ec (Product S T)) hFinite.
  have hFlat:FM (Product S T)=a%:E:=hValue.
  rewrite hFlat -EFinM.
  apply:(@extended_supremum_product_bound R
    (@current_flat_dual_values R h2 m i A hA KA (ea S))
    (@current_flat_dual_values R h2 n j B hB KB (eb T))
    (FK S) (FL T) (c * a) _ _
    (@CurrentFlatDualSeminorm.laws R h2 m i A hA KA (ea S))
    (@CurrentFlatDualSeminorm.laws R h2 n j B hB KB (eb T))
    (mulr_ge0 (ltW hc) ha) hDef).
  + exists 0;split.
    * by rewrite (real_seminorm_zero (@current_flat_test_is_seminorm R h2 m i A hA KA)) ler01.
    * exact:linear0.
  + exists 0;split.
    * by rewrite (real_seminorm_zero (@current_flat_test_is_seminorm R h2 n j B hB KB)) ler01.
    * exact:linear0.
  + move=>u [alpha [hAlpha <-]] v [beta [hBeta <-]].
    have hPure:FC (Pure alpha beta)<=c.
      apply:(le_trans (@current_cartesian_flat_test_bound R h2 m n A B hA hB
        KA KB KAB hKAB i j alpha beta)).
      have hProduct:FA alpha * FB beta<=1.
        have h:=ler_pM
          (real_seminorm_nonnegative (@current_flat_test_is_seminorm R h2 m i A hA KA) alpha)
          (real_seminorm_nonnegative (@current_flat_test_is_seminorm R h2 n j B hB KB) beta)
          hAlpha hBeta.
        by rewrite mulr1 in h.
      have h:=ler_wpM2l (ltW hc) hProduct;by rewrite mulr1 in h.
    have hAction:=@current_flat_dual_finite_bound R h2 (m+n) (i+j) AB hAB KAB
      (ec (Product S T)) a hValue (Pure alpha beta).
    rewrite ((@CartesianCurrentProduct.laws R h2 m n i j A B hA hB S T).1 alpha beta)
      normrM in hAction.
    apply:(le_trans hAction).
    have h:=ler_wpM2l ha hPure.
    by rewrite [a*c]mulrC in h.
- have hInfinity:FM (Product S T)=(+oo)%E.
    by apply/eqP;rewrite eq_le leey hFinite.
  rewrite hInfinity (gt0_muley (lte_tofin hc));exact:leey.
Qed.
End CurrentFlatCartesianLower.
