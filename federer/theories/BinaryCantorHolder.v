(** Federer (1969), 3.4.4, p. 318: the
    printed sharp Holder coefficient for the original correspondence. *)
From mathcomp Require Import all_boot all_order all_algebra finmap boolp classical_sets
  reals topology lra.
From Federer Require Import RealMetricBackground CompactIntervalGauge SpecialIntervalFamilyUP
  BinaryCantorCodingUP BinaryCantorCodingLaws BinaryCantorFirstSplit BinaryCantorMatchingUP
  RealPower RealPowerContinuity BinaryCantorScalePowers.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope fset_scope.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [binary_original_correspondence_holder]: the
    two displayed distance estimates and their Holder consequence,
    3.4.4, p. 318. The original common parent
    bounds target distance; its two children give the exact
    source gap. Positivity of the exponent converts these
    estimates without losing the printed coefficient. *)
Theorem binary_original_correspondence_holder (R:realType) (rho sigma p:R)
    JA HA I a JB HB J b A B phi:
  is_binary_original_coding rho JA HA I a ->
  is_binary_original_coding sigma JB HB J b ->
  is_special_interval_tree_limit HA A ->0<rho ->0<1-2*rho ->0<p ->
  (forall j,sigma^+j=real_power (rho^+j) p) ->
  is_binary_cantor_correspondence A B I J phi ->
  forall (x y:real_line_metric R),A x ->A y ->
    `|phi x-phi y|<=real_power (1-2*rho) (-p)*real_power `|x-y| p.
Proof.
move=>hI hJ hA hRho hGap hP hScale hPhi x y hx hy.
case:(eqVneq x y)=>hSame.
- subst y;by rewrite !subrr normr0 real_power_zero_base ?gt_eqF // mulr0.
- have [w [c [d [hBits [hX [hY hBound]]]]]]:=
    @binary_original_first_split R rho JA HA I a A hI hA hRho hGap x y hx hy hSame.
  have hUpper:rho<=1 by nra.
  have hParentX:=@binary_original_coding_child_subset R rho JA HA I a hI (ltW hRho) hUpper w c x hX.
  have hParentY:=@binary_original_coding_child_subset R rho JA HA I a hI (ltW hRho) hUpper w d y hY.
  have hTargetX:=binary_cantor_correspondence_intervals hPhi hx hParentX.
  have hTargetY:=binary_cantor_correspondence_intervals hPhi hy hParentY.
  have hTargetBound:=@binary_original_coding_point_distance R sigma JB HB J b hJ w
    (phi x) (phi y) hTargetX hTargetY.
  rewrite hScale in hTargetBound.
  have hPowerPositive:0<rho^+(size w) by rewrite exprn_gt0.
  have hProduct:=@real_power_monotone R ((1-2*rho)*rho^+(size w)) `|x-y| p
    (mulr_ge0 (ltW hGap) (ltW hPowerPositive)) hBound hP.
  have hPowered:real_power (1-2*rho) p*real_power (rho^+(size w)) p<=real_power `|x-y| p.
    move:hProduct;by rewrite (@real_power_product R (1-2*rho) (rho^+(size w)) p (ltW hGap) (ltW hPowerPositive)).
  have hCoefficient:0<real_power (1-2*rho) p:=@real_power_strictly_positive R (1-2*rho) p hGap.
  have hNonzero:real_power (1-2*rho) p!=0 by rewrite gt_eqF.
  have hInv:0<=(real_power (1-2*rho) p)^-1 by rewrite invr_ge0;exact:ltW hCoefficient.
  have hRealBound:=ler_wpM2l hInv hPowered.
  rewrite mulrA mulVf // mul1r in hRealBound.
  apply:le_trans hTargetBound _.
  by rewrite real_power_negative_exponent //.
Qed.

(** Source for [binary_cantor_printed_holder_bound]: the
    precise Holder estimate in 3.4.4, p. 318,
    for the original alpha and beta constructions. The
    coefficient remains (1-2*2^(-1/alpha))^(-alpha/beta). *)
Theorem binary_cantor_printed_holder_bound (R:realType) (alpha beta:R)
    JA HA I a JB HB J b A B phi:
  0<alpha ->alpha<1 ->0<beta ->
  is_binary_original_coding (real_power 2 (-alpha^-1)) JA HA I a ->
  is_binary_original_coding (real_power 2 (-beta^-1)) JB HB J b ->
  is_special_interval_tree_limit HA A ->
  is_binary_cantor_correspondence A B I J phi ->
  forall (x y:real_line_metric R),A x ->A y ->
  `|phi x-phi y|<=real_power (1-2*real_power 2 (-alpha^-1)) (-(alpha/beta))*
    real_power `|x-y| (alpha/beta).
Proof.
move=>hAlpha hAlphaUpper hBeta hI hJ hA hPhi.
have [hRho hGap]:=binary_cantor_scale_bounds hAlpha hAlphaUpper.
have hP:0<alpha/beta by rewrite divr_gt0.
exact:(@binary_original_correspondence_holder R (real_power 2 (-alpha^-1))
  (real_power 2 (-beta^-1)) (alpha/beta) JA HA I a JB HB J b A B phi
  hI hJ hA (andP hRho).1 hGap hP
  (binary_cantor_scale_power hAlpha hBeta) hPhi).
Qed.
