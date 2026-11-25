(** Private existence witness for the continuous polarity in Federer
    (1969), 3.1.1, p. 209. The abstract dual laws supply each representing
    functional; their injectivity proves linearity of the assembled map. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp.
From Federer Require Import Hom Bilinear InnerProductUP InnerProductLaws
  InnerNorm InnerNormInequalities RealNormUP ContinuousDualUP
  ContinuousRealFunctional ContinuousPolarityUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [continuous_polarity_exists]: existence of the polarity
    used in Federer 3.1.1, p. 209. Cauchy's inequality ensures each inner
    product evaluation belongs to the continuous dual. Completeness is
    unnecessary for this direction; it is needed only for surjectivity. *)
Lemma continuous_polarity_exists (R : realType) (V D : lmodType R)
    (B : V -> V -> R) (hB : is_inner_product B)
    (hN : is_real_norm (inner_norm hB))
    (evaluation : Hom D (Hom V R^o)) (DN : D -> R) :
  is_continuous_dual hN evaluation DN ->
  exists P : Hom V D, is_continuous_polarity B evaluation P.
Proof.
move=> hD.
have hex : forall u : V, exists d : D, forall v, evaluation d v = B v u.
  move=> u.
  pose F := @HomMap R V R^o (fun v => B v u)
    (introT (asboolP _) ((inner_bilinear hB).1 u)).
  have hF : is_continuous_real_functional hN (hom_as_linear F).
    apply: (@bounded_real_functional_continuous R V (inner_norm hB) hN
      (hom_as_linear F) (inner_norm hB u) (inner_norm_nonnegative hB u))=> v.
    change (`|B v u| <= inner_norm hB u * inner_norm hB v).
    rewrite mulrC; exact: inner_cauchy.
  have [d hd] := continuous_dual_surjective hD hF.
  exists d=> v; by rewrite hd.
pose p := fun u => sval (constructive_indefinite_description (hex u)).
have hp : forall u v, evaluation (p u) v = B v u.
  move=> u; exact: (svalP (constructive_indefinite_description (hex u))).
have hlin : linear p.
  move=> c u v; apply: (continuous_dual_injective hD); apply: hom_ext=> w.
  rewrite hp linearD linearZ hom_addE hom_scaleE !hp.
  exact: ((inner_bilinear hB).2 w c u v).
exists (@HomMap R V D p (introT (asboolP _) hlin)); exact hp.
Qed.
