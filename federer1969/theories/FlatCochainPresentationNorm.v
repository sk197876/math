(** Federer (1969), 4.1.19, p. 377: the
    cochain norm is the exact dual norm
    of its functional on the original L1
    pair space. This supporting presentation theorem
    consumes precisely the two cost assertions of
    4.1.18, p. 375, without equating fixed-K
    norms with a norm on the whole union. *)
From mathcomp Require Import all_boot all_order all_algebra
  classical_sets reals constructive_ereal topology.
From Federer Require Import Hom RealNormUP NormDifferentialUP InnerNorm
  HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  CurrentSpaces SmoothCompactSet CurrentFlatNorm FlatCurrentsUP
  FlatCurrentUnionSpace FlatCochainUP FlatCochainSpace RealFunctionalNormUP
  SeminormFunctionalSignedUnitBall ExtendedScaledErrorBound.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section PresentationNorm.
Variable R : realType.
Hypothesis h2 : (1+1:R)!=0.
Variables n m : nat.
Variable U : set (R_n R n).
Hypothesis hU : forall x, U x -> norm_domain_interior
  (inner_norm (@euclidean_inner_productP R n)) U x.
Local Notation hNX :=
  (inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation W := (@flat_current_union_space R h2 n m U hU).
Local Notation inc := (@flat_current_union_inclusion R h2 n m U hU).
Local Notation FK := (@current_flat_norm R h2 n m U hU).
Local Notation flatK := (@is_flat_current_supported_in R h2 n m U hU).
Local Notation A := (@flat_cochain_space R h2 n m U hU).
Local Notation E := (@flat_cochain_evaluation R h2 n m U hU).
Local Notation N := (@flat_cochain_norm R h2 n m U hU).
Variable P : lmodType R.
Variable J : P -> R.
Hypothesis hJ : is_real_seminorm J.
Variable q : Hom P W.
Hypothesis hFirst : forall v : P,
  exists K : smooth_compact_set hNX U,
    flatK K (inc (q v)) /\ fine (FK K (inc (q v))) <= J v.
Hypothesis hSecond : forall (K : smooth_compact_set hNX U) (T : W),
  flatK K (inc T) -> forall delta : R, 0 < delta ->
  exists v : P, q v = T /\ J v <= fine (FK K (inc T))+delta.

(** Source for [flat_cochain_presentation_functional_norm]:
    the exact norm of beta in Federer 4.1.19,
    p. 377, follows from the preceding
    two original cost assertions in 4.1.18,
    p. 375. The second is used with
    an arbitrary positive error, removed by the
    registered vanishing-error bound. No minimizer is assumed. *)
Theorem flat_cochain_presentation_functional_norm (alpha : A) :
  is_real_functional_norm J (hom_as_linear (hom_comp (E alpha) q)) (N alpha).
Proof.
have hNorm := @flat_cochain_norm_laws R h2 n m U hU alpha.
constructor.
- exact: hNorm.1.1.
- move=> v.
  have [K [hFlat hCost]] := @hFirst v.
  rewrite hom_as_linearE hom_compE.
  exact: (le_trans (hNorm.1.2 K (q v) hFlat)
    (ler_wpM2l hNorm.1.1 hCost)).
- move=> c hC hBeta.
  apply: (hNorm.2 c); split; first exact: hC.
  move=> K T hFlat.
  have hLimit : ((`|E alpha T|)%:E <= (c*fine (FK K (inc T)))%:E)%E.
    apply: (@extended_upper_bound_from_scaled_errors R
      (`|E alpha T|)%:E (c*fine (FK K (inc T))) c hC).
    move=> delta hDelta.
    have [v [hQ hCost]] := @hSecond K T hFlat delta hDelta.
    have h := hBeta v.
    rewrite hom_as_linearE hom_compE hQ in h.
    rewrite lee_fin -mulrDr.
    exact: (le_trans h (ler_wpM2l hC hCost)).
  by rewrite lee_fin in hLimit.
Qed.

(** Source for [flat_cochain_presentation_signed_supremum]:
    the literal display F(alpha)=sup beta[J<=1]
    in Federer 4.1.19, p. 377.
    The signed closed ball contains zero and
    includes every raw null-field case. This
    statement does not assume the supremum is attained. *)
Theorem flat_cochain_presentation_signed_supremum (alpha : A) :
  N alpha = sup [set E alpha (q v) | v in [set v | J v <= 1]].
Proof.
have hNorm := flat_cochain_presentation_functional_norm alpha.
have [hUpper hLeast] :=
  @seminorm_functional_norm_signed_unit_lub R P J hJ
    (hom_comp (E alpha) q) (N alpha) hNorm.
pose B := [set E alpha (q v) | v in [set v | J v <= 1]].
have hNonempty : B !=set0.
  exists 0; exists (0:P).
  - change (is_true (J (0:P)<=1)).
    by rewrite (real_seminorm_zero hJ) ler01.
  - by rewrite !linear0.
have hBound : ubound B (N alpha).
  move=> t [v hv <-]; exact: hUpper v hv.
have hHasUpper : has_ubound B by exists (N alpha).
apply/eqP; rewrite eq_le; apply/andP; split.
- apply: hLeast=> v hv.
  exact: (sup_upper_bound (conj hNonempty hHasUpper)
    (imageP (fun z => E alpha (q z)) hv)).
- exact: (ge_sup hNonempty hBound).
Qed.
End PresentationNorm.
