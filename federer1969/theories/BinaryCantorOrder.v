(** Federer (1969), 3.4.4, p. 318: the
    induced correspondence preserves the original real order. *)
From mathcomp Require Import all_boot all_order all_algebra finmap boolp classical_sets
  reals topology lra.
From Federer Require Import RealMetricBackground CompactIntervalGauge SpecialIntervalFamilyUP
  BinaryCantorCodingUP BinaryCantorCodingLaws BinaryCantorFirstSplit BinaryCantorMatchingUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope fset_scope.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [binary_original_correspondence_strict_order]:
    the order-preserving correspondence of 3.4.4, p. 318.
    The first different source digits must be left and right
    in that order. The same original target digits then give
    strictly ordered target points, by the actual positive gap. *)
Theorem binary_original_correspondence_strict_order (R:realType) (rho sigma:R)
    JA HA I a JB HB J b A B phi:
  is_binary_original_coding rho JA HA I a ->
  is_binary_original_coding sigma JB HB J b ->
  is_special_interval_tree_limit HA A ->0<rho ->0<1-2*rho ->
  0<sigma ->0<1-2*sigma ->
  is_binary_cantor_correspondence A B I J phi ->
  forall (x y:real_line_metric R),A x ->A y ->x<y ->phi x<phi y.
Proof.
move=>hI hJ hA hRho hGap hSigma hTargetGap hPhi x y hx hy hLess.
have hNe:x!=y by rewrite lt_eqF.
have [w [c [d [hBits [hX [hY hBound]]]]]]:=
  @binary_original_first_split R rho JA HA I a A hI hA hRho hGap x y hx hy hNe.
have hTargetX:=binary_cantor_correspondence_intervals hPhi hx hX.
have hTargetY:=binary_cantor_correspondence_intervals hPhi hy hY.
have hSourcePositive:0<(1-2*rho)*rho^+(size w).
  apply:mulr_gt0 hGap _;by rewrite exprn_gt0.
have hTargetPositive:0<(1-2*sigma)*sigma^+(size w).
  apply:mulr_gt0 hTargetGap _;by rewrite exprn_gt0.
clear hBound.
case:c d hBits hX hY hTargetX hTargetY=>[|][|] // _ hX hY hTargetX hTargetY.
- exfalso.
  have h:=(@binary_original_coding_sibling_gap R rho JA HA I a hI w y x hY hX).1.
  nra.
- have h:=(@binary_original_coding_sibling_gap R sigma JB HB J b hJ w (phi x) (phi y) hTargetX hTargetY).1.
  nra.
Qed.
