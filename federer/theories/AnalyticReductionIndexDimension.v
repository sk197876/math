(** Federer (1969), 3.4.8(13), pp. 335–336:
    every original E_m reduction has index equal to
    the actual dimension of the irreducible variety germ.
    Retain both endpoints: the B-tail gives depth zero,
    and E_n forces full depth, including n=0. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormMetric GrassmannAbbreviations FiniteCoordinates
  FiniteDualDimension EuclideanInnerProduct InnerProductUP InnerNorm HilbertFormCompactness LinearBasis
  OrthogonalGroupTopology AnalyticGermRing AnalyticOrthogonalPullback AnalyticRotatedGermIdeal
  CommutativeIdealUP AnalyticCoordinateSubringFamilySealed AnalyticFullPrefixGermSubring
  AnalyticReductionActual AnalyticReductionLociUP AnalyticReductionDepthUP AnalyticDepthSealed
  AnalyticReductionZeroIdeal AnalyticPrimeReductionDimension SetGermUP GermVanishingSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [analytic_last_reduction_depth]: the full-prefix
    endpoint in 3.4.8(13), p. 335. A
    nonzero original ideal has a nonzero member in
    Q_n after every rotation; E_n excludes that member. *)
Lemma analytic_last_reduction_depth (R:realType) (X:lmodType R)
    (B:X->X->R) (hB:is_inner_product B) n (e:'I_n->X) (he:is_basis e)
    (omega:'I_n->Hom X R^o)
    (hDual:forall i j,omega i (e j)=if i==j then 1 else 0)
    (I:set (@analytic_germ_ring R X (inner_norm hB) (inner_norm_real_norm hB) 0))
    (g:@orthogonal_group R X B hB n e he):
  is_commutative_ideal I ->
  @analytic_reduction_actual_E R X B hB n e he omega I ord_max g ->
  @AnalyticDepth.value R X B hB n e he omega I=n.
Proof.
move=>hI hEn.
have hBound:=analytic_reduction_depth_bound (@AnalyticDepth.laws R X B hB n e he omega I).
case:(posnP n)=>[hZero|hPositive].
- apply/eqP;rewrite eqn_leq hBound /=.
  have hN0:(n<=0)%N by rewrite hZero.
  exact:leq_trans hN0 (leq0n _).
- pose NX:=inner_norm hB;pose hNX:=inner_norm_real_norm hB.
  pose G:=[the comNzRingType of (@analytic_germ_ring R X NX hNX 0)].
  have hLoci:=@analytic_reduction_actual_laws R X B hB n e he omega I.
  have hNotA:=(analytic_reduction_E_last_membership hLoci g).1 hEn.
  have hQ:=@analytic_full_prefix_germ_subring R X NX hNX n e he omega hDual.
  have hIZero:I=[set alpha:G|alpha=0].
    apply/seteqP;split.
    * move=>alpha hAlpha;apply:contrapT=>hNonzero;apply:hNotA.
      apply:(analytic_reduction_A_membership hLoci ord_max g).2;split;first exact:hPositive.
      pose M:=@analytic_orthogonal_germ_map R X B hB n e he g.
      exists (M alpha);split.
      -- apply/analytic_rotated_germ_ideal_membership;by exists alpha.
      -- split;first by rewrite hQ.
         move=>hMapZero;apply:hNonzero.
         apply:(@analytic_orthogonal_germ_map_injective R X B hB n e he g).
         by rewrite rmorph0.
    * move=>alpha ->;exact:commutative_ideal_zero hI.
  rewrite hIZero;exact:analytic_depth_zero_ideal.
Qed.

(** Source for [analytic_prime_reduction_index_dimension]: the
    only-if direction of 3.4.8(13), pp. 335–336,
    for every original integer index 0<=m<=n.
    The prime ideal is the actual vanishing ideal
    of an original set germ; no generic-coordinate
    or measure-comparison conclusion is a hypothesis. *)
Theorem analytic_prime_reduction_index_dimension (R:realType) n
    (I:set (@analytic_germ_ring R (R_n R n) (inner_norm (@euclidean_inner_productP R n))
      (inner_norm_real_norm (@euclidean_inner_productP R n)) 0))
    (m:'I_n.+1)
    (g:@orthogonal_group R (R_n R n) (@euclidean_inner_product R n)
      (@euclidean_inner_productP R n) n (@coordinate_basis R n) (@coordinate_basisP R n)):
  is_prime_commutative_ideal I ->
  (exists sigma,I=@AnalyticSetIdeal.value R (R_n R n) (inner_norm (@euclidean_inner_productP R n))
    (inner_norm_real_norm (@euclidean_inner_productP R n)) 0 sigma) ->
  @analytic_reduction_actual_E R (R_n R n) (@euclidean_inner_product R n)
    (@euclidean_inner_productP R n) n (@coordinate_basis R n) (@coordinate_basisP R n)
    (dual_basis (@coordinate_basisP R n)) I m g ->
  @AnalyticDepth.value R (R_n R n) (@euclidean_inner_product R n)
    (@euclidean_inner_productP R n) n (@coordinate_basis R n) (@coordinate_basisP R n)
    (dual_basis (@coordinate_basisP R n)) I=(m:nat).
Proof.
move=>hPrime hVanishing hEm.
pose X:=R_n R n;pose B:=@euclidean_inner_product R n;pose hB:=@euclidean_inner_productP R n.
pose e:=@coordinate_basis R n;pose he:=@coordinate_basisP R n;pose omega:=dual_basis he.
have hDual i j:omega i (e j)=if i==j then 1 else 0 by rewrite dual_basisE eq_sym.
case:(ltnP m n)=>hMN.
- pose mi:'I_n:=Ordinal hMN.
  have hIndex:widen_ord (leqnSn n) mi=m by apply:val_inj.
  have hInterior:@analytic_reduction_actual_E R X B hB n e he omega I (widen_ord (leqnSn n) mi) g.
    by rewrite hIndex.
  case:(posnP (m:nat))=>[hZero|hPositive].
  + have hLoci:=@analytic_reduction_actual_laws R X B hB n e he omega I.
    have hTail:=((analytic_reduction_E_membership hLoci mi g).1 hInterior).2.1.
    have hBound:=(analytic_reduction_depth_minimal (@AnalyticDepth.laws R X B hB n e he omega I)
      (ex_intro _ g hTail)).
    apply/eqP;rewrite eqn_leq hBound /= hZero;exact:leq0n.
  + exact:(@analytic_prime_positive_reduction_dimension R n I mi g hPrime hVanishing hPositive hInterior).
- have hEqual:(m:nat)=n by apply/eqP;rewrite eqn_leq hMN andbT;exact:ltn_ord m.
  have hIndex:m=ord_max by apply:val_inj;exact:hEqual.
  rewrite hEqual;apply:(@analytic_last_reduction_depth R X B hB n e he omega hDual I g hPrime.1).
  by rewrite -hIndex.
Qed.
