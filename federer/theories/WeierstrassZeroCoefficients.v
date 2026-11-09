(** Federer (1969), 3.4.6, p. 323: an
    actual analytic germ is zero exactly when all
    original mixed polynomial coefficients vanish. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import Hom RealNormUP AnalyticGermUP AnalyticGermJetZeroNegate
  WeierstrassCoefficientUP WeierstrassCoefficientValue WeierstrassCoefficientExistence
  WeierstrassTransverseUP WeierstrassSplitInjective.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [weierstrass_zero_coefficient_characterization]:
    the original mixed representation has zero germ
    if and only if all its coefficients are zero,
    as stated in 3.4.6, p. 323.
    Actual zero jets and proved mixed Taylor
    injectivity give both directions. *)
Theorem weierstrass_zero_coefficient_characterization (R:realType) (X K:lmodType R)
    (NX:X->R) (NK:K->R) (hNX:is_real_norm NX) (v:X)
    (xi:Hom X R^o) (inclusion:Hom K X) (projection:Hom X K)
    (alpha:analytic_germ_space hNX (0:X)) (q:nat->nat->K->R):
  is_weierstrass_transverse_space NX NK v xi inclusion projection ->
  (forall i j,is_weierstrass_split_coefficient alpha v inclusion i j (q i j)) ->
  (alpha=@analytic_germ_zero R X NX hNX 0 <->forall i j z,q i j z=0).
Proof.
move=>hSplit hQ;split.
- move=>hZero i j z.
  by rewrite (weierstrass_split_coefficient_value (hQ i j) z) hZero
    analytic_germ_jet_zero linear0 mulr0.
- move=>hZero.
  have [d hD]:=@weierstrass_split_coefficients_exist R X K NX hNX
    (@analytic_germ_zero R X NX hNX 0) v inclusion.
  have hDZero i j z:d i j z=0.
    by rewrite (weierstrass_split_coefficient_value (hD i j) z)
      analytic_germ_jet_zero linear0 mulr0.
  apply:(@weierstrass_split_coefficients_injective R X K NX NK hNX v xi inclusion projection
    alpha (@analytic_germ_zero R X NX hNX 0) q d hSplit hQ hD)=>i j z.
  by rewrite hZero hDZero.
Qed.
