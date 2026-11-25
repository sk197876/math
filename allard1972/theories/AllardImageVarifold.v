(** Allard (1972), 3.2(1), printed p. 430, specialised to M = M' = R^n;
    blueprint al:3.2. Public interface of the image varifold. Suppose
    V ∈ V_k(R^n), and F : R^n → R^n is of class 1 with derivative DF, DF(x)
    is injective for every x, and F is proper
    ([is_proper_class_one_immersion]). Then F_# V ([image_varifold]) is a
    k dimensional varifold in R^n ([allard_3_2_1_varifold]) and

        F_# V(B) = ∫_{{(x, S) : (F(x), DF(x)(S)) ∈ B}} ‖∧_k(DF(x) ∘ S)‖ dV(x, S)

    for every Borel subset B of G_k(R^n) ([allard_3_2_1]). Here DF(x)(S) is
    the orthogonal projection of R^n onto DF(x)[im S]
    ([image_bundle_map_plane]) given by the projection formula of
    new:projection_formula, and ‖∧_k(DF(x) ∘ S)‖ is the Jacobian of
    Federer 3.2.1 ([image_bundle_jacobian]). The integral form
    ∫ α dF_# V = ∫ α(F(x), DF(x)(S)) ‖∧_k(DF(x) ∘ S)‖ dV(x, S) holds for
    every real valued Borel function α, in particular for every continuous
    α ([allard_3_2_1_integral], [allard_3_2_1_continuous_integral]); and
    F_# V is the only measure with these properties
    ([allard_3_2_1_unique]). *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets functions reals
  constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerNorm InnerMetric
  LinearBasis FiniteCoordinates Hom HomInner ExtendedRealOrderTopology PartialFunctionUP MeasureUP
  RadonMeasureUP TopologicalBorel BorelFunctionUP BorelFunctionBasic MeasureIntegralUP
  SummableRealFunctionUP MeasureStepIntegralIdentification CharacteristicFunctionUP
  RealMetricBackground.
From Allard Require Import AllardOrthogonalProjectors AllardProjectionFormula.
From Allard Require Export AllardGrassmann AllardVarifolds AllardImageVarifoldMaps
  AllardImageVarifoldUP.
From Allard Require Import AllardImageVarifoldSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section ImageVarifold.
Variable R : realType.
Variables n k : nat.
Local Notation Rn := (R_n R n).
Local Notation hBn := (@euclidean_inner_productP R n).
Local Notation hbn := (@coordinate_basisP R n).
Local Notation GB := (grassmann_bundle R n k).

(** Source for [image_varifold]: Allard 3.2, p. 430: the image F_# V of
    a varifold V under F, for M = M' = R^n. Definition. *)
Definition image_varifold (F : Rn -> Rn) (DF : Rn -> Hom Rn Rn) (V : set GB -> \bar R) :
    set GB -> \bar R :=
  @ImageVarifold.value R n k F DF V.

(** Source for [image_varifoldP]: Allard 3.2(1), p. 430: F_# V has the
    characteristic property [is_image_varifold]. Direct formalisation. *)
Theorem image_varifoldP (F : Rn -> Rn) (DF : Rn -> Hom Rn Rn) (V : set GB -> \bar R) :
  is_varifold V -> is_proper_class_one_immersion F DF ->
  is_image_varifold F DF V (image_varifold F DF V).
Proof. exact: ImageVarifold.laws. Qed.

(** Source for [allard_3_2_1_varifold]: Allard 3.2, p. 430: F_# V is a
    Radon measure over G_k(R^n), that is F_# V ∈ V_k(R^n). Direct
    formalisation. *)
Theorem allard_3_2_1_varifold (F : Rn -> Rn) (DF : Rn -> Hom Rn Rn) (V : set GB -> \bar R) :
  is_varifold V -> is_proper_class_one_immersion F DF -> is_varifold (image_varifold F DF V).
Proof. by move=> hV hF; exact: (image_varifold_is_varifold (image_varifoldP hV hF)). Qed.

(** Source for [allard_3_2_1]: Allard 3.2(1), p. 430:
    F_# V(B) = ∫ s_B(F(x), DF(x)(S)) ‖∧_k(DF(x) ∘ S)‖ dV(x, S) whenever B
    is a Borel subset of G_k(R^n) and s_B is its characteristic function.
    Direct formalisation. *)
Theorem allard_3_2_1 (F : Rn -> Rn) (DF : Rn -> Hom Rn Rn) (V : set GB -> \bar R)
    (B : set GB) (s : GB -> R) :
  is_varifold V -> is_proper_class_one_immersion F DF ->
  borel_set B -> is_characteristic_function B s ->
  is_measure_integral V (real_total_integrand
    (fun z : GB => s (image_bundle_map F DF z) * image_bundle_jacobian DF z))
    (image_varifold F DF V B).
Proof. by move=> hV hF hB hs; exact: (image_varifold_borel_set (image_varifoldP hV hF) hB hs). Qed.

(** Source for [allard_3_2_1_integral]: Allard 3.2(1), p. 430, in
    integral form: ∫ α dF_# V = ∫ α(F(x), DF(x)(S)) ‖∧_k(DF(x) ∘ S)‖ dV(x, S)
    for every real valued Borel function α on G_k(R^n), as an equivalence
    of integral values (either side may be infinite or undefined). Direct
    formalisation. *)
Theorem allard_3_2_1_integral (F : Rn -> Rn) (DF : Rn -> Hom Rn Rn) (V : set GB -> \bar R)
    (alpha : GB -> R) :
  is_varifold V -> is_proper_class_one_immersion F DF ->
  is_borel_function (alpha : GB -> real_line_metric R) ->
  forall a, is_measure_integral (image_varifold F DF V) (real_total_integrand alpha) a <->
    is_measure_integral V (real_total_integrand
      (fun z : GB => alpha (image_bundle_map F DF z) * image_bundle_jacobian DF z)) a.
Proof. by move=> hV hF ha; exact: (image_varifold_integral (image_varifoldP hV hF) ha). Qed.

(** Source for [allard_3_2_1_continuous_integral]: Allard 3.2(1),
    p. 430, in integral form for a continuous function α on G_k(R^n).
    Direct formalisation. *)
Theorem allard_3_2_1_continuous_integral (F : Rn -> Rn) (DF : Rn -> Hom Rn Rn)
    (V : set GB -> \bar R) (alpha : GB -> R) :
  is_varifold V -> is_proper_class_one_immersion F DF ->
  continuous (alpha : GB -> real_line_metric R) ->
  forall a, is_measure_integral (image_varifold F DF V) (real_total_integrand alpha) a <->
    is_measure_integral V (real_total_integrand
      (fun z : GB => alpha (image_bundle_map F DF z) * image_bundle_jacobian DF z)) a.
Proof.
move=> hV hF ha; apply: (allard_3_2_1_integral hV hF).
exact: (continuous_borel_function ha).
Qed.

(** Source for [allard_3_2_1_unique]: Allard 3.2, p. 430: F_# V "is
    characterised by the requirement" 3.2(1). Direct formalisation. *)
Theorem allard_3_2_1_unique (F : Rn -> Rn) (DF : Rn -> Hom Rn Rn) (V W : set GB -> \bar R) :
  is_varifold V -> is_proper_class_one_immersion F DF ->
  is_image_varifold F DF V W -> W = image_varifold F DF V.
Proof. by move=> hV hF hW; exact: (image_varifold_unique hW (image_varifoldP hV hF)). Qed.

(** Source for [image_bundle_map_plane]: Allard 3.2, p. 430, with
    blueprint new:projection_formula: if DF(x) is injective, the second
    component of F_♮(x, S) is the orthogonal projection of R^n onto
    DF(x)[im S]; its image is DF(x)[im S]. Supporting lemma. *)
Lemma image_bundle_map_plane (F : Rn -> Rn) (DF : Rn -> Hom Rn Rn) (z : GB) (y : Rn) :
  (forall x, injective (DF x)) ->
  (exists w, (set_val (image_bundle_map F DF z).2 : Hom Rn Rn) w = y) <->
  (exists x, DF z.1 ((set_val z.2 : Hom Rn Rn) x) = y).
Proof.
move=> hinj.
have hA : injective (projection_formula_operator (DF z.1) (set_val z.2 : Hom Rn Rn)).
  exact: (proj2 (projection_formula_operator_injective_jacobian (DF z.1) (projection_grassmannP z.2))
    (image_bundle_jacobian_positive hinj z)).
rewrite /image_bundle_map /= (projection_grassmann_imageE hA).
exact: (projection_formula_map_image hA
  (orthogonal_projector_idempotent (projection_grassmannP z.2)) y).
Qed.
End ImageVarifold.
