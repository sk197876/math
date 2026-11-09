(** Federer (1969), 3.3.19, p. 305: uniform actual
    cyclic cap counts under the proved 2/n coordinate
    perturbation. All original cap half-angles are retained. *)
From mathcomp Require Import all_boot all_order all_algebra finmap reals boolp classical_sets topology lra ring.
From Federer Require Import EuclideanInnerProduct InnerNorm InnerMetric RealTrigonometryUP CircularTrigonometryUP
  CircularTrigonometrySealed CircularRegularDirections CircularRegularCapCount CircularRegularCapLowerCount
  CircularCosineUniformGap.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope fset_scope.
Local Open Scope ring_scope.
Section Counts.
Variable R:realType.
Local Notation E:=(inner_metric_space (@euclidean_inner_productP R 2)).
Local Notation hE:=(@euclidean_inner_productP R 2).
Local Notation B:=(@euclidean_inner_product R 2).
Local Notation C:=(@CircularTrigonometry.cosine R).
Local Notation S:=(@CircularTrigonometry.sine R).
Local Notation p:=(@CircularTrigonometry.half_period R).

(** Source for [finite_cyclic_subfamily_fraction_bounds]:
    actual cyclic-index fractions lie in [0,1], supporting
    endpoint cap estimates in 3.3.19, p. 305. *)
Lemma finite_cyclic_subfamily_fraction_bounds n (F:{fset 'I_n}):(0<n)%N ->
  (0<=#|` F|%:R/n%:R:>R) /\(#|` F|%:R/n%:R<=1:>R).
Proof.
move=>hn.
have hPositive:(0<n%:R:>R) by rewrite ltr0n.
have hSubset:(F `<=` [fset k | k:'I_n])%fset.
  apply/fsubsetP=>k _;apply/imfsetP;by exists k.
have hCard:= fsubset_leq_card hSubset.
have hTotal:#|` [fset k | k:'I_n]|= n by rewrite card_imfset //= -cardE card_ord.
rewrite hTotal in hCard.
split.
- apply:divr_ge0;by rewrite ler0n.
- rewrite ler_pdivrMr // mul1r ler_nat;exact:hCard.
Qed.

(** Source for [circular_perturbed_cap_upper_count]: a
    subfamily whose original coordinates are at least
    cos(gamma)-2/n has fraction at most
    gamma/pi+e/pi+1/n once the proved uniform cosine
    margin dominates 2/n. This supports the uniform
    original cap comparison in 3.3.19, p. 305. *)
Theorem circular_perturbed_cap_upper_count n (u:E) (e gamma:R) (F:{fset 'I_n}):
  (0<n)%N ->inner_norm hE u= 1 ->0<e ->e<p ->0<=gamma ->gamma<=p ->
  2/n%:R<2*(S (e/2))^+2 ->
  (forall k,k \in F ->C gamma-2/n%:R<=B (@circular_regular_direction R n k) u) ->
  #|` F|%:R/n%:R<=gamma/p+e/p+1/n%:R.
Proof.
move=>hn hu he hep hGamma hGammaP hSmall hCoordinate.
have hp:= real_trigonometry_pi_positive (circular_trig_basic (@CircularTrigonometry.laws R)).
have hNP:(0<n%:R:>R) by rewrite ltr0n.
case:(leP gamma (p-e))=>hInterior.
- have [_ hGap]:= @circular_cosine_uniform_gap R e gamma he hep hGamma hInterior.
  have hOuterNonnegative:0<=gamma+e by lra.
  have hOuterUpper:gamma+e<=p by lra.
  have hCap k:k \in F ->C (gamma+e)<=B (@circular_regular_direction R n k) u.
    move=>hk;have hOriginal:= hCoordinate k hk;lra.
  have hCount:= @circular_regular_cap_subfamily_count R n u (gamma+e) F
    hn hu hOuterNonnegative hOuterUpper hCap.
  by rewrite mulrDl in hCount.
- have hFraction:=(@finite_cyclic_subfamily_fraction_bounds n F hn).2.
  have hRatio:1<=gamma/p+e/p.
    rewrite -mulrDl ler_pdivlMr // mul1r;lra.
  have hInverse:(0<=1/n%:R:>R) by apply:divr_ge0;[exact:ler01|by rewrite ler0n].
  lra.
Qed.

(** Source for [circular_perturbed_cap_lower_count]: if
    the original subfamily contains all directions with
    coordinate at least cos(gamma)+2/n, its fraction is
    at least gamma/pi-e/pi-1/n under the same actual
    uniform cosine margin. This retains the zero-angle
    case in the cap comparison of 3.3.19, p. 305. *)
Theorem circular_perturbed_cap_lower_count n (u:E) (e gamma:R) (F:{fset 'I_n}):
  (0<n)%N ->inner_norm hE u= 1 ->0<e ->e<p ->0<=gamma ->gamma<=p ->
  2/n%:R<2*(S (e/2))^+2 ->
  (forall k,C gamma+2/n%:R<=B (@circular_regular_direction R n k) u ->k \in F) ->
  gamma/p-e/p-1/n%:R<=#|` F|%:R/n%:R.
Proof.
move=>hn hu he hep hGamma hGammaP hSmall hContains.
have hp:= real_trigonometry_pi_positive (circular_trig_basic (@CircularTrigonometry.laws R)).
case:(leP e gamma)=>hInterior.
- have hInnerNonnegative:0<=gamma-e by lra.
  have hInnerUpper:gamma-e<=p by lra.
  have hMargin:gamma-e<=p-e by lra.
  have [_ hGap]:= @circular_cosine_uniform_gap R e (gamma-e) he hep hInnerNonnegative hMargin.
  have hAngle:(gamma-e)+e= gamma by ring.
  rewrite hAngle in hGap.
  have hCap k:C (gamma-e)<=B (@circular_regular_direction R n k) u ->k \in F.
    move=>hOriginal;apply:hContains;lra.
  have hCount:= @circular_regular_cap_containing_count R n u (gamma-e) F
    hn hu hInnerNonnegative hInnerUpper hCap.
  by rewrite mulrBl in hCount.
- have hFraction:=(@finite_cyclic_subfamily_fraction_bounds n F hn).1.
  have hRatio:gamma/p-e/p<=0.
    rewrite -mulrBl.
    have hInv:0<p^-1 by rewrite invr_gt0.
    have hNumerator:gamma-e<=0 by lra.
    have hScaled:=ler_wpM2r (ltW hInv) hNumerator.
    by rewrite mul0r in hScaled.
  have hInverse:(0<=1/n%:R:>R) by apply:divr_ge0;[exact:ler01|by rewrite ler0n].
  lra.
Qed.
End Counts.
