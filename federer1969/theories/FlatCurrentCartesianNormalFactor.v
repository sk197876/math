(** Federer (1969), 4.1.12, p. 369: a normal
    first factor and a flat second factor give a
    flat product in the exact compact product index.
    Use the original normal approximants and the
    preceding constant-one normal-times-flat estimate. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal lra.
From Federer Require Import Hom Bilinear RealNormUP NormDifferentialUP InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct EuclideanCartesianMap CurrentSpaces SmoothCompactSet
  CurrentCartesianDomain CurrentCartesianProductSealed CurrentCartesianProductBilinear
  CurrentCartesianCompactSupportBound CurrentCartesianNormal CurrentSupportGeometry
  NormalCurrentsUP CurrentNormalMass NormalCurrentFiniteMass CurrentFlatNorm CurrentFlatDualSeminormSealed
  CurrentFlatDualSeminormBasic CurrentFlatCartesianFiniteUpper FlatCurrentsUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section FlatCurrentCartesianNormalFactor.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables m n i j:nat.
Local Notation NX := (inner_norm (@euclidean_inner_productP R m)).
Local Notation NY := (inner_norm (@euclidean_inner_productP R n)).
Local Notation hNX := (inner_norm_real_norm (@euclidean_inner_productP R m)).
Local Notation hNY := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation hNZ := (inner_norm_real_norm (@euclidean_inner_productP R (m+n))).
Variables (A:set (R_n R m)) (B:set (R_n R n)).
Hypothesis hA:forall a,A a->norm_domain_interior NX A a.
Hypothesis hB:forall b,B b->norm_domain_interior NY B b.
Local Notation AB := (@euclidean_cartesian_set R m n A B).
Local Notation hAB := (@current_cartesian_domain_open R m n A B hA hB).
Variables (KA:smooth_compact_set hNX A) (KB:smooth_compact_set hNY B)
  (KAB:smooth_compact_set hNZ AB).
Hypothesis hKAB:smooth_compact_carrier KAB=
  @euclidean_cartesian_set R m n (smooth_compact_carrier KA) (smooth_compact_carrier KB).
Local Notation CA := (@current_space R h2 m A hA i).
Local Notation CB := (@current_space R h2 n B hB j).
Local Notation P := (@CartesianCurrentProduct.value R h2 m n i j A B hA hB).
Local Notation N := (@current_normal_mass R h2 m A hA i).
Local Notation FD := (@current_flat_norm R h2 n j B hB KB).

(** Source for [flat_current_cartesian_normal_factor]:
    S in N_(i,C)(A) and T in F_(j,D)(B) imply
    S times T in F_(i+j,C times D)(A times B),
    the original closure conclusion of Federer
    4.1.12, p. 369. No positivity or
    representation restriction is imposed on T. *)
Theorem flat_current_cartesian_normal_factor (S:CA) (T:CB):
  @normal_currents_supported_in R h2 m A hA i KA S->
  @is_flat_current_supported_in R h2 n j B hB KB T->
  @is_flat_current_supported_in R h2 (m+n) (i+j) AB hAB KAB (P S T).
Proof.
move=>[hNormal hSupport] hFlat epsilon hEpsilon.
have hNFinite:=@normal_current_finite_normal_mass R h2 m A hA i S hNormal.
have hN0:=@current_normal_mass_nonnegative R h2 m A hA i S.
have hNumber:N S \is a fin_num by rewrite (ge0_fin_numE hN0).
pose a:=fine (N S).
have hNValue:N S=a%:E by rewrite /a fineK.
have ha:0<=a by move:hN0;rewrite hNValue lee_fin.
have hDenominator:0<a+1 by lra.
pose delta:=epsilon/(a+1).
have hDelta:0<delta by rewrite /delta divr_gt0.
have [Q [[hNormalQ hSupportQ] hApprox]]:=@hFlat delta hDelta.
have hErrorFinite:(FD ((T-Q)%R) < +oo)%E:=lt_trans hApprox (ltry delta).
have [b [hb hBValue]]:=@current_flat_dual_finite_value R h2 n j B hB KB
  (@current_value R h2 n B hB j (T-Q)) hErrorFinite.
have hFlatValue:FD ((T-Q)%R)=b%:E:=hBValue.
have hbDelta:b<delta by move:hApprox;rewrite hFlatValue lte_fin.
have hProduct:=@current_flat_cartesian_finite_upper R h2 m n A B hA hB KA KB KAB hKAB
  i j S (T-Q) a b hNValue hFlatValue hSupport.
have hRealError:a * b<epsilon.
  have hFirst:=ler_wpM2l ha (ltW hbDelta).
  have hStrict:a * delta<(a+1) * delta.
    rewrite (ltr_pM2r hDelta);lra.
  have hEndpoint:(a+1) * delta=epsilon.
    by rewrite /delta mulrC divfK ?gt_eqF.
  rewrite hEndpoint in hStrict;exact:le_lt_trans hFirst hStrict.
exists (P S Q);split.
- split.
  + exact:(@normal_current_cartesian_product R h2 m n A B hA hB i j S Q hNormal hNormalQ).
  + exact:(@current_cartesian_compact_support_bound R h2 m n i j A B hA hB KA KB KAB hKAB
      S Q hSupport hSupportQ).
- have hLinear:=(@current_cartesian_product_bilinear R h2 m n i j A B hA hB).2 S.
  rewrite -(linB hLinear).
  apply:(le_lt_trans hProduct);by rewrite lte_fin.
Qed.
End FlatCurrentCartesianNormalFactor.
