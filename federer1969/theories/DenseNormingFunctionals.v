(** Supporting dual-separability argument in Federer (1969), 2.9.22, p. 167:
    a separable reflexive space has separable dual. The present step selects
    norming functionals on a dense set and proves they separate points.
    Hahn–Banach is supplied by 2.4.12, pp. 86–87. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals topology lra.
From Federer Require Import Hom RealNormUP NormMetric ContinuousRealFunctional
  RealFunctionalNormUP ContinuousDualUP SeparableClosedCover.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [is_dual_norming_family]: supporting specification
    for a family of unit-bounded norming functionals in the
    separability reduction of Federer 2.9.22, p. 167.
    Hahn–Banach, 2.4.12, pp. 86–87, proves existence;
    this record introduces no unproved global assumption. *)
Record is_dual_norming_family (R : realType) (E D : lmodType R)
    (N : E -> R) (ed : Hom D (Hom E R^o)) (DN : D -> R) (k : E -> D) : Prop := {
  (** Source for [dual_norming_family_unit]: supporting unit dual
      bound for Federer 2.9.22, p. 167, from 2.4.12, p. 87. *)
  dual_norming_family_unit : forall y, DN (k y)<=1;
  (** Source for [dual_norming_family_value]: supporting norming
      identity for Federer 2.9.22, p. 167, from 2.4.12, pp. 86–87. *)
  dual_norming_family_value : forall y, ed (k y) y=N y;
  (** Source for [dual_norming_family_bound]: supporting evaluation
      bound for Federer 2.9.22, p. 167, from 2.4.12, p. 87. *)
  dual_norming_family_bound : forall y z, `|ed (k y) z|<=N z
}.

(** Source for [dual_norming_family_exists]: supporting norming
    family for Federer 2.9.22, p. 167, obtained by the
    proved Hahn–Banach corollary of 2.4.12, pp. 86–87.
    The result is existential; downstream arguments use only
    the preceding family laws, not the selected representatives. *)
Theorem dual_norming_family_exists (R : realType) (E D : lmodType R)
    (N : E -> R) (hN : is_real_norm N)
    (ed : Hom D (Hom E R^o)) (DN : D -> R)
    (hD : is_continuous_dual hN ed DN) :
  exists k : E -> D, is_dual_norming_family N ed DN k.
Proof.
have hone y : exists d : D, DN d<=1 /\ ed d y=N y /\
    forall z, `|ed d z|<=N z.
  have [a [ha [hb hay]]] := continuous_norming_real_functional hN y.
  have [d hd] := continuous_dual_surjective hD (a:=hom_of_linear a) ha.
  exists d; split.
    apply: (real_functional_norm_least (continuous_dual_norm_laws hD d) ler01).
    by move=> z; rewrite hom_as_linearE hd hom_of_linearE mul1r.
  split; first by rewrite hd hom_of_linearE.
  by move=> z; rewrite hd hom_of_linearE.
have [k hk] := choice hone.
exists k; constructor=> y; [exact: (hk y).1|exact: (hk y).2.1|exact: (hk y).2.2].
Qed.

(** Source for [dense_norming_family_separates]: supporting
    totality of the countable norming family in Federer's
    separable-dual reduction, 2.9.22, p. 167. Approximate a
    nonzero vector y by a dense point c. If its norming
    functional annihilated y, then N(c)<=N(c-y), contradicting
    N(y)<=N(y-c)+N(c). Reflexivity is not needed for this step. *)
Lemma dense_norming_family_separates (R : realType) (E D : lmodType R)
    (N : E -> R) (hN : is_real_norm N)
    (ed : Hom D (Hom E R^o)) (DN : D -> R) (k : E -> D)
    (hk : is_dual_norming_family N ed DN k)
    (C : set (real_norm_metric_space hN)) :
  dense C -> forall y : E, (forall c, C c -> ed (k c) y=0) -> y=0.
Proof.
move=> hC y hy; apply: contrapT=> hn.
have hp : 0<N y by rewrite (real_norm_positive hN.1 hN.2); exact/eqP.
have he : 0<N y/3 by rewrite divr_gt0 // ltr0n.
have [c [hc hnear]] := metric_dense_point_near hC y he.
change (is_true (N (y-c)<N y/3)) in hnear.
have hval := dual_norming_family_value hk c.
have hb := dual_norming_family_bound hk c (c-y).
rewrite (linearB (hom_as_linear (ed (k c))) c y) !hom_as_linearE
  (hy c hc) subr0 hval (ger0_norm (real_seminorm_nonnegative hN.1 c))
  (real_seminorm_subtract hN.1 c y) in hb.
have ht := real_seminorm_triangle hN.1 (y-c) c.
rewrite subrK in ht.
exfalso; clear hn; lra.
Qed.
