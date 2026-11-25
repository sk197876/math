(** Federer (1969), 3.4.8(1), p. 326:
    the zero-coordinate subring Q_0 is exactly the
    scalar constants. Actual germs on R^0 have constant
    representatives, and the original pullback preserves them. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import Hom RealNormUP LinearBasis GrassmannAbbreviations
  EuclideanInnerProduct InnerNorm HilbertFormCompactness AnalyticGermRepresentatives
  AnalyticGermUP AnalyticGermRingLaws AnalyticGermRing AnalyticGermTrivialSource
  AnalyticPrefixGermMap AnalyticPrefixGermMapLaws AnalyticPrefixGermSubring.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [analytic_prefix_zero_subring_constants]: the
    original Q_0=R convention is an equality with actual
    constant germs, 3.4.8(1), p. 326. The source
    and ambient zero-dimensional cases remain. *)
Theorem analytic_prefix_zero_subring_constants (R:realType) (X:lmodType R)
    (NX:X->R) (hNX:is_real_norm NX) n (e:'I_n->X) (he:is_basis e)
    (omega:'I_n->Hom X R^o) (alpha:@analytic_germ_ring R X NX hNX 0):
  @analytic_prefix_germ_subring R X NX hNX n e he omega 0 (leq0n n) alpha <->
  exists c:R,alpha=analytic_germ (@analytic_constant_representative R X NX hNX 0 c).
Proof.
pose Y:=R_n R 0.
pose NY:=inner_norm (@euclidean_inner_productP R 0).
pose hNY:=inner_norm_real_norm (@euclidean_inner_productP R 0).
pose E:=@analytic_prefix_germ_map R X NX hNX n e he omega 0 (leq0n n).
have hTrivial (z:Y):z=0.
  apply/ffunP=>i;by have:=ltn_ord i;rewrite ltn0.
split.
- move=>/analytic_prefix_germ_subring_membership[beta hBeta].
  have [f hF]:=@analytic_germ_has_representative R Y NY hNY 0 beta.
  have hConstant:=@analytic_germ_trivial_source_constant R Y NY hNY 0 f hTrivial.
  exists (analytic_representative_value f 0).
  rewrite -hBeta -hF hConstant.
  exact:(@analytic_prefix_germ_map_constant R X NX hNX n e he omega 0 (leq0n n) _).
- move=>[c ->];apply/analytic_prefix_germ_subring_membership.
  exists (analytic_germ (@analytic_constant_representative R Y NY hNY 0 c)).
  exact:(@analytic_prefix_germ_map_constant R X NX hNX n e he omega 0 (leq0n n) c).
Qed.
