(** Federer (1969), 2.3.8, p. 78: supporting pointwise algebra for the
    translation-invariant pseudodistance. Source context and partial-domain
    correction: PartialNormedArithmetic.v. Identities hold on the stated
    common domains; they are not identities of partial graphs with
    potentially different domains. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal.
From Federer Require Import RealNormUP PartialFunctionUP PartialNormedArithmetic MeasureGauge.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [partial_norm_difference_symmetric_superlevel]:
    symmetry of difference norm superlevels for the pseudodistance
    in Federer 2.3.8, p. 78; both differences have exactly
    the same common domain. *)
Lemma partial_norm_difference_symmetric_superlevel (R : realType) (X : Type) (V : lmodType R)
    (N : V -> R) (hN : is_real_seminorm N) (f g : partial_function X V) r :
  partial_norm_superlevel N (partial_vector_subtract f g) r =
    partial_norm_superlevel N (partial_vector_subtract g f) r.
Proof.
have hi : forall a b : partial_function X V,
    partial_norm_superlevel N (partial_vector_subtract a b) r `<=`
    partial_norm_superlevel N (partial_vector_subtract b a) r.
  move=> a b x [z [hz hn]].
  have [a0 [b0 [ha [hb he]]]] := proj1 (partial_vector_subtract_graph a b x z) hz.
  exists (b0-a0)%R; split.
  - apply: (proj2 (partial_vector_subtract_graph b a x _)); exists b0,a0; by split=> //; split.
  - have hn' : r < (N z)%:E := hn.
    rewrite he (real_seminorm_subtract hN) in hn'; exact hn'.
apply/seteqP; split; exact: hi.
Qed.

(** Source for [partial_difference_telescope_agreement]: supporting
    telescoping identity for the triangle inequality in Federer
    2.3.8, p. 78. The middle function must be defined;
    this is later an almost-everywhere condition. *)
Lemma partial_difference_telescope_agreement (K : fieldType) (X : Type) (V : lmodType K)
    (f g h : partial_function X V) x :
  partial_function_domain f x -> partial_function_domain g x -> partial_function_domain h x ->
  partial_function_agreement
    (partial_vector_add (partial_vector_subtract f g) (partial_vector_subtract g h))
    (partial_vector_subtract f h) x.
Proof.
move=> [a ha] [b hb] [c hc]; exists (a-c)%R; split.
- apply: (proj2 (partial_vector_add_graph _ _ x _)); exists (a-b)%R,(b-c)%R; split.
  + apply: (proj2 (partial_vector_subtract_graph f g x _)); exists a,b; by split=> //; split.
  + split.
    * apply: (proj2 (partial_vector_subtract_graph g h x _)); exists b,c; by split=> //; split.
    * by rewrite addrA subrK.
- apply: (proj2 (partial_vector_subtract_graph f h x _)); exists a,c; by split=> //; split.
Qed.

(** Source for [partial_difference_translation_agreement]: supporting
    translation identity for Federer 2.3.8, p. 78.
    Adding the same partial function may shrink both domains;
    their norms agree on the triple common domain. *)
Lemma partial_difference_translation_agreement (K : fieldType) (X : Type) (V : lmodType K)
    (f g h : partial_function X V) x :
  partial_function_domain f x -> partial_function_domain g x -> partial_function_domain h x ->
  partial_function_agreement
    (partial_vector_subtract (partial_vector_add f h) (partial_vector_add g h))
    (partial_vector_subtract f g) x.
Proof.
move=> [a ha] [b hb] [c hc]; exists (a-b)%R; split.
- apply: (proj2 (partial_vector_subtract_graph _ _ x _)); exists (a+c)%R,(b+c)%R; split.
  + apply: (proj2 (partial_vector_add_graph f h x _)); exists a,c; by split=> //; split.
  + split.
    * apply: (proj2 (partial_vector_add_graph g h x _)); exists b,c; by split=> //; split.
    * by rewrite opprD addrACA subrr addr0.
- apply: (proj2 (partial_vector_subtract_graph f g x _)); exists a,b; by split=> //; split.
Qed.
