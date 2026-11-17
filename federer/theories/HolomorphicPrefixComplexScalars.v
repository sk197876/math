(** Federer (1969), 3.4.12, p. 339, extending 3.4.8(1),(8), pp. 326, 330:
    the original prefix pullback preserves
    the original complex constant germs. Apply
    its existing constant representative equation. *)
From mathcomp Require Import all_boot all_order all_algebra boolp reals.
From Federer Require Import ScalarRestriction ComplexScalarSealed ComplexNormUP FiniteCoordinates HolomorphicCoordinateNorm Hom RealNormUP LinearBasis GrassmannAbbreviations EuclideanInnerProduct
  InnerNorm HilbertFormCompactness HolomorphicGermRing HolomorphicScalarsSealed
  HolomorphicPrefixGermMap HolomorphicPrefixGermMapLaws.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [holomorphic_prefix_complex_scalar_triangle]:
    the copy of C in the original
    prefix ring agrees with the copy
    of R in the original ambient germ
    ring, supporting the primitive-coordinate calculation
    of 3.4.8(8), p. 330. *)
Lemma holomorphic_prefix_complex_scalar_triangle (R:realType) (X:lmodType (ComplexScalars.C R))
  (NX:X->R) (hNX:@is_real_norm R (restricted_space (ComplexScalars.embed R) X) NX) n (e:'I_n->X) (he:is_basis e)
  (omega:'I_n->Hom X (ComplexScalars.C R)^o) m (hMN:(m<=n)%N) (c:ComplexScalars.C R):
  @holomorphic_prefix_germ_map R X NX hNX n e he omega m hMN
    (@HolomorphicScalars.map R (coordinate_space (ComplexScalars.C R) m) (@holomorphic_coordinate_norm R m)
      (complex_norm_real (@holomorphic_coordinate_norm_laws R m)) 0 c) =
    @HolomorphicScalars.map R X NX hNX 0 c.
Proof.
rewrite (@HolomorphicScalars.laws R (coordinate_space (ComplexScalars.C R) m) (@holomorphic_coordinate_norm R m)
  (complex_norm_real (@holomorphic_coordinate_norm_laws R m)) 0 c) holomorphic_prefix_germ_map_constant.
exact:esym (@HolomorphicScalars.laws R X NX hNX 0 c).
Qed.
