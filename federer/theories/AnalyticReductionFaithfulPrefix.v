(** Federer (1969), 3.4.8(10), p. 330:
    exclusion from the original A_m makes
    the original quotient coefficient map
    faithful. Apply exact A_m membership,
    quotient kernels and the proved prefix
    pullback injection. The printed m>0 remains. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets functions reals.
From Federer Require Import Hom RealNormUP InnerProductUP InnerNorm HilbertFormCompactness
  LinearBasis GrassmannAbbreviations EuclideanInnerProduct OrthogonalGroupTopology AnalyticGermRing
  AnalyticPrefixGermMap AnalyticPrefixGermSubring AnalyticPrefixGermInjective
  AnalyticCoordinateSubringFamilyUP AnalyticCoordinateSubringFamilySealed AnalyticRotatedGermIdeal
  AnalyticReductionLociUP AnalyticReductionActual CommutativeQuotientUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [analytic_reduction_not_A_faithful_prefix]:
    p restricted to the original Q_m
    is a monomorphism under the original
    not-A_m condition, 3.4.8(10), p. 330.
    The actual O_0(R^m) prefix map is
    used, with its injectivity already proved. *)
Theorem analytic_reduction_not_A_faithful_prefix (R:realType) (X:lmodType R)
  (B:X->X->R) (hB:is_inner_product B) n (e:'I_n->X) (he:is_basis e)
  (omega:'I_n->Hom X R^o) (hDual:forall i k,omega i (e k) = if i==k then 1 else 0)
  (I:set (@analytic_germ_ring R X (inner_norm hB) (inner_norm_real_norm hB) 0))
  (g:@orthogonal_group R X B hB n e he) (C:comNzRingType)
  (pi:{rmorphism [the comNzRingType of (@analytic_germ_ring R X (inner_norm hB)
    (inner_norm_real_norm hB) 0)]->C}) (m:'I_n) (hMN:((m:nat)<=n)%N):
  is_commutative_ideal_quotient (@analytic_rotated_germ_ideal R X B hB n e he I g) pi ->
  (0<m)%N ->~@analytic_reduction_actual_A R X B hB n e he omega I (widen_ord (leqnSn n) m) g ->
  injective (fun a=>pi (@analytic_prefix_germ_map R X (inner_norm hB) (inner_norm_real_norm hB)
    n e he omega m hMN a)).
Proof.
move=>hPi hPositive hNotA a b hEqual.
pose E:=@analytic_prefix_germ_map R X (inner_norm hB) (inner_norm_real_norm hB) n e he omega m hMN.
pose alpha:=E (a-b).
have hKernel:@analytic_rotated_germ_ideal R X B hB n e he I g alpha.
  apply:(commutative_quotient_kernel hPi _).1.
  by rewrite /alpha !rmorphB hEqual subrr.
have hQ:=@AnalyticCoordinateSubringFamily.laws R X (inner_norm hB) (inner_norm_real_norm hB) n e he omega.
have hMember:@AnalyticCoordinateSubringFamily.value R X (inner_norm hB) (inner_norm_real_norm hB)
    n e he omega m alpha.
  rewrite (analytic_coordinate_subring_family_member hQ hMN).
  apply/analytic_prefix_germ_subring_membership;by exists (a-b).
have hLoci:=@analytic_reduction_actual_laws R X B hB n e he omega I.
have hZero:alpha = 0.
  apply:contrapT=>hNonzero;apply:hNotA.
  apply:(analytic_reduction_A_membership hLoci (widen_ord (leqnSn n) m) g).2.
  split;first exact:hPositive.
  exists alpha;by split;last split.
have hInjective:=@analytic_prefix_germ_map_injective R X (inner_norm hB) (inner_norm_real_norm hB)
  n e he omega hDual m hMN.
have hDifference:a-b = 0.
  apply:hInjective;change (alpha = E 0);by rewrite hZero rmorph0.
by apply/eqP;rewrite -subr_eq0 hDifference eqxx.
Qed.
