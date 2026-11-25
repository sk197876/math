(** Federer (1969), 4.1.24, p. 382: the
    original mass distance separates currents. Its zero
    value annihilates every actual compact test by the
    preceding finite mass estimate, and the original
    dual-space equality law gives zero. No separate
    representation or support premise is needed. *)
From mathcomp Require Import all_boot all_order all_algebra
  classical_sets reals constructive_ereal.
From Federer Require Import Hom Bilinear RealNormUP NormDifferentialUP
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  CurrentSpaces CurrentEvaluation CurrentMassSealed CurrentMassTestBound.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [current_mass_zero_implies_zero]: zero original
    mass identifies the zero current, as required by
    the mass metric of 4.1.24, p. 382. Empty
    opens and degree zero use the same actual tests. *)
Theorem current_mass_zero_implies_zero (R:realType) (h2:(1+1:R)!=0) n m
    (U:set (R_n R n))
    (hU:forall x,U x->norm_domain_interior
      (inner_norm (@euclidean_inner_productP R n)) U x)
    (T:@current_space R h2 n U hU m):
  @CurrentMass.value R h2 n m U hU T=0%E->T=0.
Proof.
move=>hMass;apply:(@current_values_extensional R h2 n m U hU)=>phi.
have[a [ha hPhi]]:=@current_test_positive_comass_bound R h2 n m U hU phi.
have hBound:=@current_finite_mass_test_bound R h2 n m U hU T phi a 0 hMass ha hPhi.
rewrite mulr0 normr_le0 in hBound.
rewrite (lin0 (hom_linear (@current_value R h2 n U hU m))) hom_zeroE.
apply/eqP;exact:hBound.
Qed.
