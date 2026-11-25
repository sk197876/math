(** Allard (1972), 3.2(1), printed p. 430, specialised to M = M' = R^n;
    blueprint al:3.2. Suppose V ∈ V_k(R^n) and F : R^n → R^n is of class 1
    with derivative DF. Allard characterises the image varifold F_# V by

        F_# V(B) = ∫_{{(x, S) : (F(x), DF(x)(S)) ∈ B}} ‖∧_k(DF(x) ∘ S)‖ dV(x, S)

    for Borel subsets B of G_k(R^n). This file states the characteristic
    property as a predicate ([is_image_varifold]): W is a Radon measure over
    G_k(R^n) and

        ∫ α dW = ∫ α(F(x), DF(x)(S)) ‖∧_k(DF(x) ∘ S)‖ dV(x, S)

    for every real valued Borel function α on G_k(R^n), as an equivalence
    of integral values. It derives Allard's formula for Borel sets
    ([image_varifold_borel_set]) and the uniqueness of W
    ([image_varifold_unique]). The standing hypotheses on F are collected in
    [is_proper_class_one_immersion]: F is of class 1, DF(x) is injective
    for every x, and F is proper; a diffeomorphism of R^n onto R^n has
    these properties. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets functions reals
  constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerNorm InnerMetric
  LinearBasis FiniteCoordinates Hom ExtendedRealOrderTopology PartialFunctionUP MeasureUP MeasureBasic
  RadonMeasureUP RadonBorelRegularity BorelRegularMeasureUP TopologicalBorel BorelFunctionUP
  BorelFunctionBasic MeasurableFunctionUP MeasureIntegralUP SummableRealFunctionUP
  MeasureStepIntegralIdentification MeasureIntegralUniqueness MeasureCharacteristicIntegral
  CharacteristicFunctionUP CharacteristicFunctionSealed CharacteristicBorel NormClassOneUP
  ProperMapUP RealMetricBackground.
From Allard Require Import AllardGrassmann AllardVarifolds AllardImageVarifoldMaps.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section ImageVarifoldUP.
Variable R : realType.
Variables n k : nat.
Local Notation Rn := (R_n R n).
Local Notation hBn := (@euclidean_inner_productP R n).
Local Notation RnM := (inner_metric_space hBn).
Local Notation GB := (grassmann_bundle R n k).

(** Source for [is_proper_class_one_immersion]: Allard 3.2, p. 430,
    hypotheses on the map F, specialised to M = M' = R^n: F is of class 1
    with derivative DF (Federer 3.1.1, p. 210), DF(x) is injective for
    every x, and F is proper. These hold for a diffeomorphism of R^n onto
    R^n; they make F_# V a Radon measure (see docs/divergences.md).
    Definition. *)
Record is_proper_class_one_immersion (F : Rn -> Rn) (DF : Rn -> Hom Rn Rn) : Prop := {
  (** Source for [immersion_class_one]: F is of class 1 with derivative
      DF, Federer 3.1.1, p. 210. *)
  immersion_class_one : is_norm_class_one_field (inner_norm hBn) (inner_norm hBn) setT F DF;
  (** Source for [immersion_injective]: DF(x) is injective for every x. *)
  immersion_injective : forall x, injective (DF x);
  (** Source for [immersion_proper]: F is proper, Federer 2.2.17. *)
  immersion_proper : is_proper_map (fun x : RnM => (F x : RnM))
}.

(** Source for [is_image_varifold]: Allard 3.2(1), p. 430: W is the
    image F_# V of V under F. The measure W over G_k(R^n) is a Radon
    measure, and ∫ α dW = ∫ α(F(x), DF(x)(S)) ‖∧_k(DF(x) ∘ S)‖ dV(x, S) for
    every real valued Borel function α on G_k(R^n), as an equivalence of
    integral values (Federer 2.4.2). Definition. *)
Record is_image_varifold (F : Rn -> Rn) (DF : Rn -> Hom Rn Rn) (V W : set GB -> \bar R) : Prop := {
  (** Source for [image_varifold_measure]: F_# V is a measure over
      G_k(R^n), Allard 3.2, p. 430. *)
  image_varifold_measure : is_measure W;
  (** Source for [image_varifold_radon]: F_# V is a Radon measure,
      Allard 3.2, p. 430, under the hypotheses of
      [is_proper_class_one_immersion]. *)
  image_varifold_radon : is_radon_measure W;
  (** Source for [image_varifold_integral]: Allard 3.2(1), p. 430, in
      integral form. *)
  image_varifold_integral : forall alpha : GB -> R,
    is_borel_function (alpha : GB -> real_line_metric R) ->
    forall a, is_measure_integral W (real_total_integrand alpha) a <->
      is_measure_integral V (real_total_integrand
        (fun z : GB => alpha (image_bundle_map F DF z) * image_bundle_jacobian DF z)) a
}.

(** Source for [image_varifold_is_varifold]: Allard 3.2, p. 430:
    F_# V ∈ V_k(R^n). Supporting lemma. *)
Lemma image_varifold_is_varifold (F : Rn -> Rn) (DF : Rn -> Hom Rn Rn) (V W : set GB -> \bar R) :
  is_image_varifold F DF V W -> is_varifold W.
Proof. by move=> hW; split; [exact: image_varifold_measure hW|exact: image_varifold_radon hW]. Qed.

(** Source for [image_varifold_borel_set]: Allard 3.2(1), p. 430:
    F_# V(B) = ∫ s_B(F(x), DF(x)(S)) ‖∧_k(DF(x) ∘ S)‖ dV(x, S) for every
    Borel subset B of G_k(R^n), where s_B is the characteristic function
    of B (Federer 2.2.14). Direct formalisation. *)
Lemma image_varifold_borel_set (F : Rn -> Rn) (DF : Rn -> Hom Rn Rn) (V W : set GB -> \bar R)
    (B : set GB) (s : GB -> R) :
  is_image_varifold F DF V W -> borel_set B -> is_characteristic_function B s ->
  is_measure_integral V (real_total_integrand
    (fun z : GB => s (image_bundle_map F DF z) * image_bundle_jacobian DF z)) (W B).
Proof.
move=> hW hB hs.
have hm := image_varifold_measure hW.
have hr := image_varifold_radon hW.
have hsb : is_borel_function (s : GB -> real_line_metric R).
  exact: (proj1 (@characteristic_function_borel_iff R GB B s hs) hB).
have hBm : measure_measurable W B :=
  borel_regular_borel_measurable hm (radon_borel_regular hm hr) hB.
have hi := @measure_characteristic_integral R GB W hm B s hs hBm.
exact: (proj1 (image_varifold_integral hW hsb (W B)) hi).
Qed.

(** Source for [image_varifold_open_eq]: Allard 3.2, p. 430: "F_# V is
    characterised by the requirement" 3.2(1); two measures with the
    property of [is_image_varifold] agree on open sets. Supporting
    lemma. *)
Lemma image_varifold_open_eq (F : Rn -> Rn) (DF : Rn -> Hom Rn Rn) (V W1 W2 : set GB -> \bar R)
    (U : set GB) :
  is_image_varifold F DF V W1 -> is_image_varifold F DF V W2 -> open U -> W1 U = W2 U.
Proof.
move=> h1 h2 hU.
pose s := @CharacteristicFunction.value R GB U.
have hs : is_characteristic_function U s := @CharacteristicFunction.laws R GB U.
have hUb : borel_set U := open_borel_set hU.
have i1 := image_varifold_borel_set h1 hUb hs.
have i2 := image_varifold_borel_set h2 hUb hs.
exact: (measure_integral_unique i1 i2).
Qed.

(** Source for [image_varifold_unique]: Allard 3.2, p. 430: F_# V "is
    characterised by the requirement" 3.2(1). Since both measures are
    Radon measures, the values on open sets determine all values
    (Federer 2.2.5). Direct formalisation. *)
Theorem image_varifold_unique (F : Rn -> Rn) (DF : Rn -> Hom Rn Rn) (V W1 W2 : set GB -> \bar R) :
  is_image_varifold F DF V W1 -> is_image_varifold F DF V W2 -> W1 = W2.
Proof.
move=> h1 h2; apply: funext=> A; apply/eqP; rewrite eq_le; apply/andP; split.
- apply: (radon_outer_greatest (image_varifold_radon h2))=> U hU hAU.
  rewrite -(image_varifold_open_eq h1 h2 hU).
  exact: (measure_mono (image_varifold_measure h1) hAU).
- apply: (radon_outer_greatest (image_varifold_radon h1))=> U hU hAU.
  rewrite (image_varifold_open_eq h1 h2 hU).
  exact: (measure_mono (image_varifold_measure h2) hAU).
Qed.
End ImageVarifoldUP.
