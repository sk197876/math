(** Federer (1969), 3.1.1, p. 209: polarity is an isometric
    isomorphism onto the continuous dual in finite dimension or in a
    complete inner-product space. These proofs use only abstract laws. *)
From mathcomp Require Import all_boot all_order all_algebra reals lra.
From Federer Require Import Hom Bilinear InnerProductUP InnerProductLaws
  InnerNorm InnerNormInequalities RealNormUP ContinuousDualUP
  RealFunctionalNormUP NormDifferentialUP DifferentialGradientUP
  DifferentialGradientSealed ContinuousPolarityUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [continuous_polarity_injective]: injectivity of the
    polarity in Federer 3.1.1, p. 209, from positive definiteness alone. *)
Lemma continuous_polarity_injective (R : realType) (V D : lmodType R)
    (B : V -> V -> R) (hB : is_inner_product B)
    (evaluation : Hom D (Hom V R^o)) (P : Hom V D) :
  is_continuous_polarity B evaluation P -> injective P.
Proof.
move=> hP u v huv.
have hz : u-v = 0.
  apply: (inner_right_separates hB)=> w.
  by rewrite (bilBr (inner_bilinear hB)) -(hP u w) -(hP v w) huv subrr.
by apply/eqP; rewrite -subr_eq0 hz eqxx.
Qed.

(** Source for [continuous_polarity_isometric]: the normed-space
    polarity of Federer 3.1.1, p. 209, preserves the norm. Cauchy's
    inequality gives the upper bound; evaluation on u gives the reverse. *)
Lemma continuous_polarity_isometric (R : realType) (V D : lmodType R)
    (B : V -> V -> R) (hB : is_inner_product B)
    (hN : is_real_norm (inner_norm hB))
    (evaluation : Hom D (Hom V R^o)) (DN : D -> R) (P : Hom V D) :
  is_continuous_dual hN evaluation DN ->
  is_continuous_polarity B evaluation P -> forall u, DN (P u) = inner_norm hB u.
Proof.
move=> hD hP u; have hn := continuous_dual_norm_laws hD (P u).
have hnon := inner_norm_nonnegative hB u.
have hu : DN (P u) <= inner_norm hB u.
  apply: (real_functional_norm_least hn hnon)=> v.
  rewrite hom_as_linearE hP mulrC; exact: inner_cauchy.
have hl := real_functional_norm_bound hn u.
rewrite hom_as_linearE hP -(inner_norm_sqr hB) ger0_norm ?sqr_ge0 // in hl.
have hn0 := real_functional_norm_nonnegative hn.
by nra.
Qed.

(** Source for [continuous_polarity_surjective]: onto-ness of the
    polarity in Federer 3.1.1, p. 209. The finite-dimensional and complete
    cases use the already sealed gradient representation; no coordinates
    or Hilbert projection construction are exposed here. *)
Lemma continuous_polarity_surjective (R : realType) (V D : lmodType R)
    (B : V -> V -> R) (hB : is_inner_product B)
    (hN : is_real_norm (inner_norm hB))
    (evaluation : Hom D (Hom V R^o)) (DN : D -> R) (P : Hom V D) :
  differential_gradient_space hB -> is_continuous_dual hN evaluation DN ->
  is_continuous_polarity B evaluation P -> forall d : D, exists u, P u = d.
Proof.
move=> hspace hD hP d.
have hb : norm_bounded_linear (inner_norm hB) (fun t : R^o => `|t|) (evaluation d).
  exists (DN d); split.
  - exact: real_functional_norm_nonnegative (continuous_dual_norm_laws hD d).
  - exact: real_functional_norm_bound (continuous_dual_norm_laws hD d).
pose u := @DifferentialGradient.value R V B hB hspace (evaluation d) hb.
exists u; apply: (continuous_dual_injective hD); apply: hom_ext=> v.
rewrite hP; exact: esym (@DifferentialGradient.laws R V B hB hspace (evaluation d) hb v).
Qed.
