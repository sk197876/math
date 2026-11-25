(** Supporting continuous-dual restriction for Federer (1969), 2.9.22, p.
    167, the closed-subspace reflexivity reduction. The map from Y* to the
    subspace dual is specified by evaluation and its norm bound, before
    existence or surjectivity is proved. The dual norm is the one in 2.4.12,
    p. 87. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import Hom ModuleQuotient SubspaceCarrier RealNormUP NormedSubspace
  ContinuousDualUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [is_subspace_dual_restriction]: supporting
    specification of the dual restriction map used for the
    closed-subspace assertion in Federer 2.9.22, p. 167.
    It is characterised by the actual subspace inclusion,
    and restriction does not increase the dual norm. *)
Record is_subspace_dual_restriction (R : realType) (E D F : lmodType R)
    (Z : subspace E) (ed : Hom D (Hom E R^o))
    (ef : Hom F (Hom (subspace_space Z) R^o)) (DN : D -> R) (FN : F -> R)
    (r : Hom D F) : Prop := {
  (** Source for [subspace_dual_restriction_evaluation]: supporting
      restriction evaluation for Federer 2.9.22, p. 167,
      from the dual pairing of 2.4.12, p. 87. *)
  subspace_dual_restriction_evaluation : forall a z, ef (r a) z=ed a (subspace_val z);
  (** Source for [subspace_dual_restriction_bound]: supporting
      norm bound for Federer 2.9.22, p. 167, from the
      least evaluation bound of 2.4.12, p. 87. *)
  subspace_dual_restriction_bound : forall a, FN (r a)<=DN a
}.
Arguments is_subspace_dual_restriction {R E D F} Z ed ef DN FN r.

(** Source for [subspace_dual_restriction_unique]: supporting
    uniqueness of dual restriction in Federer 2.9.22, p. 167.
    The abstract subspace dual separates its elements by
    evaluation; no chosen dual carrier is inspected. *)
Lemma subspace_dual_restriction_unique (R : realType) (E D F : lmodType R)
    (N : E -> R) (hN : is_real_norm N) (Z : subspace E)
    (ed : Hom D (Hom E R^o)) (ef : Hom F (Hom (subspace_space Z) R^o))
    (DN : D -> R) (FN : F -> R)
    (hF : is_continuous_dual (subspace_norm_laws hN Z) ef FN) (r s : Hom D F) :
  is_subspace_dual_restriction Z ed ef DN FN r ->
  is_subspace_dual_restriction Z ed ef DN FN s -> r=s.
Proof.
move=> hr hs; apply: hom_ext=> a; apply: (continuous_dual_injective hF).
apply: hom_ext=> z.
by rewrite (subspace_dual_restriction_evaluation hr) (subspace_dual_restriction_evaluation hs).
Qed.
