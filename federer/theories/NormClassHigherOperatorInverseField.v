(** Federer (1969), 3.1.11, p. 220:
    a class-k field of linear isomorphisms
    has a class-k inverse field. A fixed
    isomorphism identifies the two operator spaces;
    no completeness of either space is assumed. *)
From mathcomp Require Import all_boot all_order all_algebra boolp reals.
From Federer Require Import Hom AlgebraUP RealNormUP AlgebraInverseUP NormDifferentialUP
  ContinuousOperatorUP ContinuousOperatorNorm ContinuousOperatorComposition
  ContinuousOperatorAlgebraUP ContinuousOperatorAlgebraSealed
  ContinuousOperatorAlgebraLaws ContinuousMultilinearUP ContinuousMultilinearSealed
  NormBilinearFixedMaps NormClassHigherUP NormClassHigherInverseField
  NormClassHigherPostcompose NormClassHigherLocalValues.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [norm_class_higher_operator_inverse_field]:
    the inverse-operator step in the assertion
    about class-k inverse functions, Federer 3.1.11,
    p. 220. A chosen inverse pair at
    one point reduces the assertion to inversion
    in the algebra of endomorphisms. The empty
    domain is treated separately, and no Banach
    hypothesis is added to the printed statement. *)
Theorem norm_class_higher_operator_inverse_field (R : realType)
    (T X Y P Q : lmodType R)
    (NT : T->R) (NX : X->R) (NY : Y->R)
    (hNT : is_real_norm NT) (hNX : is_real_norm NX) (hNY : is_real_norm NY)
    (ep : Hom P (Hom X Y)) (PN : P->R)
    (eq : Hom Q (Hom Y X)) (QN : Q->R)
    (hP : is_continuous_operator_space NX NY ep PN)
    (hQ : is_continuous_operator_space NY NX eq QN)
    (V W : nat->lmodType R)
    (ev : forall j, {ffun 'I_j->T}->Hom (V j) P) (VN : forall j, V j->R)
    (ew : forall j, {ffun 'I_j->T}->Hom (W j) Q) (WN : forall j, W j->R)
    (hV : forall j, is_continuous_multilinear_space NT PN (@ev j) (@VN j))
    (hW : forall j, is_continuous_multilinear_space NT QN (@ew j) (@WN j))
    (U : T->Prop) (F : T->P) (G : T->Q) k :
  (forall s, U s ->
    (forall x, eq (G s) (ep (F s) x)=x) /\
    (forall y, ep (F s) (eq (G s) y)=y)) ->
  norm_class_higher NT PN ev VN U F k ->
  norm_class_higher NT QN ew WN U G k.
Proof.
move=> hInv hF.
case: (pselect (exists s, U s))=>[[s0 hs0]|hEmpty].
2: apply: norm_class_higher_empty_domain=>s hs; apply: hEmpty; by exists s.
have hPN := continuous_operator_norm_is_norm hNY hP.
have hQN := continuous_operator_norm_is_norm hNX hQ.
pose E := @ContinuousOperatorAlgebra.space R X NX hNX.
pose ee := @ContinuousOperatorAlgebra.evaluation R X NX hNX.
pose EN := @ContinuousOperatorAlgebra.norm R X NX hNX.
have hE : is_continuous_operator_algebra NX ee EN :=
  @ContinuousOperatorAlgebra.laws R X NX hNX.
have hOpE := operator_algebra_space hE.
have hEN := operator_algebra_norm_is_norm hNX hE.
have hMul := operator_algebra_norm_product hE.
have [C [hC hCE]] := continuous_operator_composition_exists hP hQ hOpE.
have [Back [hBack hBackE]] := continuous_operator_composition_exists hQ hOpE hQ.
pose p0 := F s0.
pose q0 := G s0.
pose M := norm_bilinear_right_fixed hC.1 q0.
pose K := norm_bilinear_left_fixed hBack.1 q0.
have hM : norm_bounded_linear PN EN M.
  exact (@norm_bilinear_right_fixed_bound R P Q E PN QN EN hQN C hC.1 q0 hC).
have hK : norm_bounded_linear EN QN K.
  exact (@norm_bilinear_left_fixed_bound R Q E Q QN EN QN hQN Back hBack.1 q0 hBack).
pose Pe s := M (F s).
pose Qe s := C p0 (G s).
have hInvE s (hs : U s) : is_two_sided_algebra_inverse (Pe s) (Qe s).
  have [hGF hFG] := hInv s hs.
  have [hGF0 hFG0] := hInv s0 hs0.
  split; apply: (continuous_operator_injective hOpE); apply: hom_ext=>x;
    rewrite (operator_algebra_composition hE) (operator_algebra_identity hE)
      hom_of_linearE /=.
  - change (ee (C (F s) q0) (ee (C p0 (G s)) x)=x).
    by rewrite !hCE !hom_compE hFG hGF0.
  - change (ee (C p0 (G s)) (ee (C (F s) q0) x)=x).
    by rewrite !hCE !hom_compE hFG0 hGF.
pose S j := @ContinuousMultilinear.space R j T E NT EN hNT hEN.
pose es j := @ContinuousMultilinear.evaluation R j T E NT EN hNT hEN.
pose SN j := @ContinuousMultilinear.norm R j T E NT EN hNT hEN.
have hS j : is_continuous_multilinear_space NT EN (es j) (SN j).
  exact: ContinuousMultilinear.laws.
have hPe := @norm_class_higher_postcompose R T P E NT PN EN
  hNT hPN hEN V S ev VN es SN hV hS U F M k hM hF.
have hQe := @norm_class_higher_inverse_field R T E NT EN hNT hEN
  hMul S es SN hS U Pe Qe hInvE k hPe.
have hKG := @norm_class_higher_postcompose R T E Q NT EN QN
  hNT hEN hQN S W es SN ew WN hS hW U Qe K k hK hQe.
apply: (@norm_class_higher_domain_agreement R T Q NT QN hNT hQN
  W ew WN hW U (fun s=>K (Qe s)) G k _ hKG).
move=> s hs; apply: (continuous_operator_injective hQ); apply: hom_ext=>y.
change (eq (Back q0 (C p0 (G s))) y=eq (G s) y).
rewrite hBackE hom_compE hCE hom_compE.
by rewrite (hInv s0 hs0).2.
Qed.
