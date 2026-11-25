(** Private existence proof of the canonical bidual map in Federer (1969),
    2.4.12, p. 87. Its evaluations are continuous by the dual norm bound;
    the abstract bidual therefore represents them. Linearity follows using
    the existing algebraic linear retraction. Source context and the
    defining law: ContinuousBidualUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp reals.
From Federer Require Import Hom TensorUP LinearRetraction RealNormUP ContinuousRealFunctional
  RealFunctionalNormUP ContinuousDualUP ContinuousDualNorm ContinuousBidualUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [continuous_bidual_embedding_exists]: existence of tau in
    Federer 2.4.12, p. 87 *)
Theorem continuous_bidual_embedding_exists (R : realType) (V D B : lmodType R)
    (N : V -> R) (hN : is_real_norm N)
    (ed : Hom D (Hom V R^o)) (DN : D -> R)
    (hD : is_continuous_dual hN ed DN)
    (eb : Hom B (Hom D R^o)) (BN : B -> R)
    (hB : is_continuous_dual (continuous_dual_norm_is_norm hD) eb BN) :
  exists tau : Hom V B, is_bidual_embedding ed eb tau.
Proof.
have heval y : linear (fun d : D => ed d y).
  move=> c a b; rewrite linearP.
  change ((c *: ed a + ed b) y = c *: ed a y + ed b y).
  by rewrite hom_addE hom_scaleE.
pose ev y := @HomMap R D R^o (fun d => ed d y) (introT (asboolP _) (heval y)).
have htranspose : linear ev.
  move=> c x y; apply: hom_ext=> a.
  change (ed a (c *: x+y) = (c *: ev x+ev y) a).
  by rewrite hom_addE hom_scaleE linearP.
pose transpose := @HomMap R V (Hom D R^o) ev (introT (asboolP _) htranspose).
pose r := linear_retraction (i:=hom_as_linear eb) (continuous_dual_injective hB).
exists (hom_of_linear (linear_comp r (hom_as_linear transpose)))=> y a.
have hc : is_continuous_real_functional (continuous_dual_norm_is_norm hD)
    (hom_as_linear (ev y)).
  apply: (@bounded_real_functional_continuous R D DN
    (continuous_dual_norm_is_norm hD) _ (N y) (real_seminorm_nonnegative hN.1 y)).
  move=> d; change (`|ed d y| <= N y*DN d); rewrite mulrC.
  exact: real_functional_norm_bound (continuous_dual_norm_laws hD d) y.
have [b hb] := continuous_dual_surjective hB hc.
change (eb (r (ev y)) a = ed a y).
rewrite -hb /r linear_retractionK hb; by [].
Qed.
