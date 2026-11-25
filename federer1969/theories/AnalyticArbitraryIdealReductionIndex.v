(** Supporting the auxiliary sentence in Federer (1969), 3.4.8(5),
    p. 328: any nonempty original E_m has index equal to the least
    original reduction depth, for every original proper ideal.
    This is an algebraic extension of the prime vanishing-ideal
    index comparison; neither primeness nor reducedness is assumed. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import Hom RealNormUP InnerProductUP InnerNorm HilbertFormCompactness LinearBasis
  OrthonormalFamilies OrthogonalGroupTopology AnalyticGermRing AnalyticScalarsSealed
  AnalyticVanishingIdealSealed AnalyticVanishingIdealLaws CommutativeIdealUP CommutativeFactorizationUP
  CommutativeQuotientUP CommutativeQuotientSealed AnalyticRotatedIdealUP AnalyticIdealImageLaws
  AnalyticReductionActual AnalyticReductionLociUP AnalyticReductionDepthUP AnalyticDepthSealed
  AnalyticReductionIndexDimension QuotientLocalIdealImage AnalyticOriginalCoefficientActions
  FiniteAnalyticCoefficientDimension.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [analytic_arbitrary_ideal_reduction_index]: supporting
    sigma-compactness of the original E_m in the proof of Federer
    3.4.8(5), p. 328. Its original arbitrary proper ideal is retained.
    Finite coefficient actions and exact Taylor growth prove the
    index comparison; both original endpoints are included. *)
Theorem analytic_arbitrary_ideal_reduction_index (R:realType) (X:lmodType R)
    (B:X->X->R) (hB:is_inner_product B) n (e:'I_n->X) (he:is_basis e)
    (hON:orthonormal_family B e) (omega:'I_n->Hom X R^o)
    (hDual:forall i j,omega i (e j) = if i==j then 1 else 0)
    (I:set (@analytic_germ_ring R X (inner_norm hB) (inner_norm_real_norm hB) 0))
    (m:'I_n.+1) (g:@orthogonal_group R X B hB n e he):
  is_commutative_ideal I ->~I 1 ->
  @analytic_reduction_actual_E R X B hB n e he omega I m g ->
  @AnalyticDepth.value R X B hB n e he omega I = (m:nat).
Proof.
move=>hI hProper hEm.
pose d:=@AnalyticDepth.value R X B hB n e he omega I.
have hDepth:=@AnalyticDepth.laws R X B hB n e he omega I.
have hLoci:=@analytic_reduction_actual_laws R X B hB n e he omega I.
case:(ltnP m n)=>hLess.
- pose j:'I_n:=Ordinal hLess.
  have hIndex:widen_ord (leqnSn n) j = m by apply:val_inj.
  have hInterior:@analytic_reduction_actual_E R X B hB n e he omega I (widen_ord (leqnSn n) j) g.
    by rewrite hIndex.
  have [hC [hTail hNotA]]:=(analytic_reduction_E_membership hLoci j g).1 hInterior.
  have hLower:(d<=m)%N:=analytic_reduction_depth_minimal hDepth (ex_intro _ g hTail).
  case:(posnP (m:nat))=>[hZero|hPositive].
  + apply/eqP;rewrite eqn_leq hLower /= hZero;exact:leq0n.
  + pose NX:=inner_norm hB;pose hNX:=inner_norm_real_norm hB.
    pose G:=[the comNzRingType of (@analytic_germ_ring R X NX hNX 0)].
    pose constants:=@AnalyticScalars.map R X NX hNX 0.
    pose M:=@AnalyticVanishingIdeal.value R X NX hNX 0.
    pose C:=@CommutativeIdealQuotient.space R G constants I hI hProper.
    pose pi:=@CommutativeIdealQuotient.projection R G constants I hI hProper.
    have hPi:=@CommutativeIdealQuotient.laws R G constants I hI hProper.
    have hImage:is_analytic_ideal_image pi M (pi @` M).
      move=>c;split.
      * move=>[a ha hA];exists a;by split.
      * move=>[a [ha hA]];by exists a.
    have [hMIdeal [hMProper hMUnit]]:=@quotient_local_ideal_image G C pi I M (pi @` M)
      hPi hImage (@analytic_vanishing_ideal_is_ideal R X NX hNX 0)
      (@analytic_vanishing_ideal_proper R X NX hNX 0)
      (@analytic_proper_ideal_vanishes R X NX hNX 0 I hI hProper)
      (@analytic_vanishing_one_minus_unit R X NX hNX 0).
    have [phi [hFiniteM [hPhiConstants [hPhiMaximal hFaithful]]]]:=
      @analytic_original_finite_coefficient_action R X B hB n e he hON omega hDual I hI hProper
        C pi hPi g m (ltnW hLess) hTail.
    have [gd hTailD]:=analytic_reduction_depth_attained hDepth.
    have [psi [hFiniteD [hPsiConstants [hPsiMaximal _]]]]:=
      @analytic_original_finite_coefficient_action R X B hB n e he hON omega hDual I hI hProper
        C pi hPi gd d (analytic_reduction_depth_bound hDepth) hTailD.
    pose scalar:=GRing.RMorphism.clone R C (pi \o constants) _.
    have hIndexM:@Ordinal n.+1 m (ltnW hLess) = m by apply:val_inj.
    have hNotAM:~@analytic_reduction_actual_A R X B hB n e he omega I
        (@Ordinal n.+1 m (ltnW hLess)) g.
      by rewrite hIndexM -hIndex.
    have hUpper:((m:nat)<=d)%N:=@finite_analytic_coefficient_dimension R m d C phi psi scalar (pi @` M)
      hPhiConstants hPsiConstants hMIdeal hMProper hMUnit hPhiMaximal hPsiMaximal
      (hFaithful hLess hPositive hNotAM) hFiniteM hFiniteD.
    apply/eqP;by rewrite eqn_leq hLower hUpper.
- have hEqual:(m:nat) = n by apply/eqP;rewrite eqn_leq hLess andbT;exact:ltn_ord m.
  have hIndex:m = ord_max by apply:val_inj.
  rewrite hEqual;apply:(@analytic_last_reduction_depth R X B hB n e he omega hDual I g hI).
  by rewrite -hIndex.
Qed.
