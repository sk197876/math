(** Federer (1969), 2.4.12, p. 87: |tau(y)| = |y|. This proof uses only the
    abstract dual specifications and the proved Hahn–Banach norming
    corollary. Source context: ContinuousBidualUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import Hom RealNormUP RealFunctionalNormUP ContinuousRealFunctional
  ContinuousDualUP ContinuousDualNorm ContinuousBidualUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [continuous_bidual_isometry]: direct formalisation of the
    canonical embedding's norm identity in Federer 2.4.12, p. 87. *)
Theorem continuous_bidual_isometry (R : realType) (V D B : lmodType R)
    (N : V -> R) (hN : is_real_norm N)
    (ed : Hom D (Hom V R^o)) (DN : D -> R)
    (hD : is_continuous_dual hN ed DN)
    (eb : Hom B (Hom D R^o)) (BN : B -> R)
    (hB : is_continuous_dual (continuous_dual_norm_is_norm hD) eb BN)
    (tau : Hom V B) : is_bidual_embedding ed eb tau ->
  forall y, BN (tau y) = N y.
Proof.
move=> ht y.
have hupper : BN (tau y) <= N y.
  apply: (real_functional_norm_least (continuous_dual_norm_laws hB (tau y))
    (real_seminorm_nonnegative hN.1 y)).
  move=> a; rewrite hom_as_linearE ht mulrC.
  exact: real_functional_norm_bound (continuous_dual_norm_laws hD a) y.
have [a [ha [hab hay]]] := continuous_norming_real_functional hN y.
have [d hd] := continuous_dual_surjective hD (a:=hom_of_linear a) ha.
have hdn : DN d <= 1.
  apply: (real_functional_norm_least (continuous_dual_norm_laws hD d) ler01).
  by move=> z; rewrite hom_as_linearE hd hom_of_linearE mul1r; exact: hab.
have hh := real_functional_norm_bound (continuous_dual_norm_laws hB (tau y)) d.
rewrite hom_as_linearE ht hd hom_of_linearE hay
  (ger0_norm (real_seminorm_nonnegative hN.1 y)) in hh.
have hbound := ler_wpM2l
  (real_functional_norm_nonnegative (continuous_dual_norm_laws hB (tau y))) hdn.
rewrite mulr1 in hbound.
apply/eqP; rewrite eq_le hupper; exact: le_trans hh hbound.
Qed.

(** Source for [continuous_bidual_injective]: injectivity of
    tau used in Federer 2.4.12, p. 87; a consequence of its isometry. *)
Lemma continuous_bidual_injective (R : realType) (V D B : lmodType R)
    (N : V -> R) (hN : is_real_norm N)
    (ed : Hom D (Hom V R^o)) (DN : D -> R)
    (hD : is_continuous_dual hN ed DN)
    (eb : Hom B (Hom D R^o)) (BN : B -> R)
    (hB : is_continuous_dual (continuous_dual_norm_is_norm hD) eb BN)
    (tau : Hom V B) : is_bidual_embedding ed eb tau -> injective tau.
Proof.
move=> ht x y he.
have hh := continuous_bidual_isometry hB ht (x-y).
rewrite linearB in hh.
change (BN (tau x-tau y) = N (x-y)) in hh.
rewrite he subrr (real_seminorm_zero (continuous_dual_norm_is_norm hB).1) in hh.
have hz := hN.2 _ (esym hh).
by move/eqP: hz; rewrite subr_eq0=> /eqP.
Qed.
