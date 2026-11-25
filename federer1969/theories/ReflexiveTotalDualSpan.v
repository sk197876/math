(** Federer (1969), 2.9.22, p. 167: the assertion that a separable reflexive
    space has separable dual. This supporting step proves that a total
    family in Y* has dense linear span, using reflexivity and the proved
    Hahn–Banach separation of a point from a closed subspace. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals topology.
From Federer Require Import Hom ModuleQuotient RealNormUP NormMetric
  ContinuousRealFunctional ContinuousDualUP ContinuousDualNorm ContinuousBidualUP
  ClosedSubspaceFunctionalSeparation.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [reflexive_total_dual_closed_span]: supporting
    dense-span fact in the separability reduction of Federer
    2.9.22, p. 167. If a dual family separates points of Y,
    every closed linear subspace of Y* containing that family
    is all of Y*. Reflexivity turns a separating bidual
    functional into a vector annihilated by the whole family. *)
Theorem reflexive_total_dual_closed_span (R : realType)
    (E D B : lmodType R) (N : E -> R) (hN : is_real_norm N)
    (ed : Hom D (Hom E R^o)) (DN : D -> R)
    (hD : is_continuous_dual hN ed DN)
    (eb : Hom B (Hom D R^o)) (BN : B -> R)
    (hB : is_continuous_dual (continuous_dual_norm_is_norm hD) eb BN)
    (tau : Hom E B) (F : set D) (Z : subspace D) :
  is_bidual_embedding ed eb tau -> is_reflexive_embedding tau ->
  closed (fun a : real_norm_metric_space (continuous_dual_norm_is_norm hD) => Z a) ->
  F `<=` Z -> (forall y, (forall a, F a -> ed a y=0) -> y=0) ->
  forall a, Z a.
Proof.
move=> ht hr hZ hF htotal a; apply: contrapT=> ha.
have [f [hf [hzero hpos]]] :=
  @closed_subspace_continuous_separation R D DN
    (continuous_dual_norm_is_norm hD) Z a hZ ha.
have [b hb] := continuous_dual_surjective hB (a:=hom_of_linear f) hf.
have [y hy] := hr b.
have he z : ed z y=f z by rewrite -(ht y z) hy hb hom_of_linearE.
have hy0 : y=0.
  apply: htotal=> z hz; rewrite he; exact: hzero (hF z hz).
have hfa : f a=0 by rewrite -he hy0 linear0.
by rewrite hfa ltxx in hpos.
Qed.
