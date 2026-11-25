(** Federer (1969), 4.1.12, p. 368: scalar
    multiplication preserves the original flat closure
    and gives exactly the smaller compact K intersect
    spt gamma. The proof uses the preceding exact
    flat estimate and original normal-current stability. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets
  reals constructive_ereal lra.
From Federer Require Import Hom Bilinear RealNormUP NormDifferentialUP InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct CurrentSpaces SmoothCompactSet SmoothTestSpaces
  CurrentContraction CurrentContractionSupport CurrentTestContractionSupport CurrentSupportGeometry
  NormalCurrentsUP LocallyNormalScalarContraction CurrentFlatNorm CurrentFlatDualSeminormSealed
  CurrentFlatDualSeminormBasic CurrentFlatScalarTestProductBound CurrentFlatMultiplier FlatCurrentsUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section FlatCurrentScalarClosure.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n m:nat.
Local Notation X := (R_n R n).
Local Notation NX := (inner_norm (@euclidean_inner_productP R n)).
Local Notation hNX := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Variable U:set X.
Hypothesis hU:forall x,U x->norm_domain_interior NX U x.
Arguments hU : clear implicits.
Variable K:smooth_compact_set hNX U.
Variable gamma:@current_test_space R h2 n U hU 0%N.
Local Notation inc0 := (smooth_test_inclusion (@current_smooth_space_laws R h2 n U hU 0%N)).
Local Notation coefficient := (@current_flat_scalar_coefficient R h2 n U hU K (inc0 gamma)).
Local Notation L := (@current_flat_multiplier_compact R h2 n U hU K gamma).
Local Notation C := (@current_space R h2 n U hU m).
Local Notation action := (@current_value R h2 n U hU m).
Local Notation F := (@current_flat_norm R h2 n m U hU K).
Local Notation contract := (@current_contraction R h2 n 0%N m U hU (inc0 gamma)).

(** Source for [flat_current_scalar_multiplier_supported]:
    T in F_(m,K)(U) implies T contracted gamma
    in F_(m,K intersect spt gamma)(U), Federer
    4.1.12, p. 368. Every approximant remains
    an actual normal current with that exact
    support constraint; zero multiplier coefficients are allowed. *)
Theorem flat_current_scalar_multiplier_supported (T:C):
  @is_flat_current_supported_in R h2 n m U hU K T->
    @is_flat_current_supported_in R h2 n m U hU L (contract T).
Proof.
move=>hFlat epsilon hEpsilon.
have hCoefficient:=@current_flat_scalar_coefficient_nonnegative R h2 n U hU K (inc0 gamma).
have hDenominator:0<coefficient+1 by lra.
pose delta:=epsilon/(coefficient+1).
have hDelta:0<delta by rewrite /delta divr_gt0.
have [S [[hNormal hSupport] hApprox]]:=@hFlat delta hDelta.
have hFinite:(F ((T-S)%R) < +oo)%E:=lt_trans hApprox (ltry delta).
have [a [ha hValue]]:=@current_flat_dual_finite_value R h2 n m U hU K (action (T-S)) hFinite.
have hCurrentValue:F ((T-S)%R)=a%:E:=hValue.
have hRealApprox:a<delta by move:hApprox;rewrite hCurrentValue lte_fin.
have hError:=@current_flat_multiplier_finite_bound R h2 n m U hU K gamma (T-S) a hCurrentValue.
have hRealError:coefficient * a<epsilon.
  have hFirst:=ler_wpM2l hCoefficient (ltW hRealApprox).
  have hStrict:coefficient * delta<(coefficient+1) * delta.
    rewrite (ltr_pM2r hDelta);lra.
  have hEndpoint:(coefficient+1) * delta=epsilon.
    by rewrite /delta mulrC divfK ?gt_eqF.
  rewrite hEndpoint in hStrict;exact:le_lt_trans hFirst hStrict.
exists (contract S);split.
- split.
  + exact:(@locally_normal_compact_scalar_contraction R h2 n U hU m gamma S hNormal.1).
  + move=>x hx;rewrite current_flat_multiplier_compact_carrier;split.
    * exact:hSupport x (@current_contraction_support_subset R h2 n 0%N m U hU (inc0 gamma) S x hx).
    * exact:(@current_contraction_test_support_subset R h2 n 0%N m U hU gamma S x hx).
- rewrite -(linB (hom_linear contract)).
  apply:(le_lt_trans hError);by rewrite lte_fin.
Qed.
End FlatCurrentScalarClosure.

(** Source for [flat_current_scalar_multiplier]: the
    original full flat space F_m(U) is stable
    under every compact scalar test multiplier,
    by the preceding fixed-compact assertion of
    Federer 4.1.12, p. 368. *)
Theorem flat_current_scalar_multiplier (R:realType) (h2:(1+1:R)!=0) n m
    (U:set (R_n R n))
    (hU:forall x,U x->norm_domain_interior
      (inner_norm (@euclidean_inner_productP R n)) U x)
    (gamma:@current_test_space R h2 n U hU 0%N) (T:@current_space R h2 n U hU m):
  @is_flat_current R h2 n m U hU T->
    @is_flat_current R h2 n m U hU
      (@current_contraction R h2 n 0%N m U hU
        (smooth_test_inclusion (@current_smooth_space_laws R h2 n U hU 0%N) gamma) T).
Proof.
move=>[K hFlat];exists (@current_flat_multiplier_compact R h2 n U hU K gamma).
exact:(@flat_current_scalar_multiplier_supported R h2 n m U hU K gamma T hFlat).
Qed.
