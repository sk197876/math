(** Federer (1969), 3.4.4, p. 318: uniqueness
    and inversion of the induced original Cantor correspondence. *)
From mathcomp Require Import all_boot all_order all_algebra finmap boolp classical_sets
  reals topology lra.
From Federer Require Import RealMetricBackground CompactIntervalGauge SpecialIntervalFamilyUP
  RecurrentContraction BinaryCantorCodingUP BinaryCantorCodingLaws
  BinaryCantorAddressUniqueness BinaryCantorMatchingUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope fset_scope.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [binary_original_matched_point_unique]: the
    induced correspondence is single valued, 3.4.4, p. 318.
    Every original addressed target interval contains both candidate
    values. Its actual geometric diameter tends to zero. *)
Theorem binary_original_matched_point_unique (R:realType) (rho sigma:R)
    JA HA I a JB HB J b A (x y z:real_line_metric R):
  is_binary_original_coding rho JA HA I a ->
  is_binary_original_coding sigma JB HB J b ->
  is_special_interval_tree_limit HA A ->0<sigma ->sigma<1 ->A x ->
  (forall w,val (I w) x ->val (J w) y) ->
  (forall w,val (I w) x ->val (J w) z) ->y=z.
Proof.
move=>hI hJ hA hSigma hSigmaUpper hx hy hz.
apply/eqP;apply/negPn/negP=>hNe.
have hDistance:0<`|y-z| by rewrite normr_gt0 subr_eq0.
have hContraction:0<sigma<1 by apply/andP;split.
have [N hSmall]:=@geometric_contraction_small R sigma 1 `|y-z| hContraction ler01 hDistance.
rewrite mulr1 in hSmall.
have [w [hw hxw]]:=@binary_original_point_address_exists R rho JA HA I a A hI hA x hx N.
have hBound:=@binary_original_coding_point_distance R sigma JB HB J b hJ w y z (hy w hxw) (hz w hxw).
rewrite hw in hBound.
have hFalse:=lt_le_trans hSmall hBound;by rewrite ltxx in hFalse.
Qed.

(** Source for [binary_original_reverse_correspondence]:
    the order correspondence has the reverse address correspondence,
    supporting the homeomorphism assertion in 3.4.4, p. 318.
    Uniqueness of equal-level original addresses proves that
    a matched target point determines the same source address. *)
Lemma binary_original_reverse_correspondence (R:realType) (rho sigma:R)
    JA HA I a JB HB J b A B phi psi:
  is_binary_original_coding rho JA HA I a ->
  is_binary_original_coding sigma JB HB J b ->
  is_special_interval_tree_limit HA A ->is_special_interval_tree_limit HB B ->
  0<rho ->rho<1 ->0<sigma ->0<1-2*sigma ->
  is_binary_cantor_correspondence A B I J phi ->
  is_binary_cantor_correspondence B A J I psi ->
  forall (x:real_line_metric R),A x ->psi (phi x)=x.
Proof.
move=>hI hJ hA hB hRho hRhoUpper hSigma hGap hPhi hPsi x hx.
have hTarget:=binary_cantor_correspondence_maps hPhi hx.
apply:(@binary_original_matched_point_unique R sigma rho JB HB J b JA HA I a B
  (phi x) (psi (phi x)) x hJ hI hB hRho hRhoUpper hTarget).
- move=>w hw;exact:(binary_cantor_correspondence_intervals hPsi hTarget hw).
- move=>w hw.
  have [v [hv hxv]]:=@binary_original_point_address_exists R rho JA HA I a A hI hA x hx (size w).
  have hOther:val (J v) (phi x):=binary_cantor_correspondence_intervals hPhi hx hxv.
  have hSame:v=w:=@binary_original_address_point_unique R sigma JB HB J b hJ hSigma hGap
    (size w) v w (phi x) hv erefl hOther hw.
  by rewrite -hSame.
Qed.
