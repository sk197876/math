(** Federer (1969), 3.4.8(1),(8), pp. 326, 330:
    the original prefix pullback preserves
    the original real constant germs. Apply
    its existing constant representative equation. *)
From mathcomp Require Import all_boot all_order all_algebra boolp reals.
From Federer Require Import Hom RealNormUP LinearBasis GrassmannAbbreviations EuclideanInnerProduct
  InnerNorm HilbertFormCompactness AnalyticGermRing AnalyticScalarsSealed
  AnalyticPrefixGermMap AnalyticPrefixGermMapLaws.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [analytic_prefix_real_scalar_triangle]:
    the copy of R in the original
    prefix ring agrees with the copy
    of R in the original ambient germ
    ring, supporting the primitive-coordinate calculation
    of 3.4.8(8), p. 330. *)
Lemma analytic_prefix_real_scalar_triangle (R:realType) (X:lmodType R)
  (NX:X->R) (hNX:is_real_norm NX) n (e:'I_n->X) (he:is_basis e)
  (omega:'I_n->Hom X R^o) m (hMN:(m<=n)%N) (c:R):
  @analytic_prefix_germ_map R X NX hNX n e he omega m hMN
    (@AnalyticScalars.map R (R_n R m) (inner_norm (@euclidean_inner_productP R m))
      (inner_norm_real_norm (@euclidean_inner_productP R m)) 0 c) =
    @AnalyticScalars.map R X NX hNX 0 c.
Proof.
rewrite (@AnalyticScalars.laws R (R_n R m) (inner_norm (@euclidean_inner_productP R m))
  (inner_norm_real_norm (@euclidean_inner_productP R m)) 0 c) analytic_prefix_germ_map_constant.
exact:esym (@AnalyticScalars.laws R X NX hNX 0 c).
Qed.
