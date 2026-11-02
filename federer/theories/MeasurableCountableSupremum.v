(** Federer (1969), 2.3.2, p. 74: measurability of countable pointwise
    suprema of extended-real partial functions. The proof uses the abstract
    supremum laws and rational upper rays, keeping the intersection of the
    original domains. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  cardinality reals constructive_ereal topology.
From Federer Require Import PartialFunctionUP PartialFunctionSupremumUP PartialFunctionSupremumSealed
  ExtendedRealOrderTopology CountableOrderIntervals MeasureUP MeasureAlmostUP MeasureAlmostBasic MeasureFiniteClosure
  MeasureCountableClosure MeasurableFunctionUP MeasurableFunctionBorel MeasurableExtendedRationalRays.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [partial_supremum_strict_upper_preimage]: supporting
    upper-ray formula for the supremum in Federer 2.3.2, p. 74.
    The common domain remains an explicit factor, including when
    the index family is empty. *)
Lemma partial_supremum_strict_upper_preimage (R : realType) (X J : Type) (D : set J)
    (f : J -> partial_function X (extended_real_line R))
    (g : partial_function X (extended_real_line R)) (hg : is_partial_function_supremum D f g)
    (t : \bar R) :
  partial_function_preimage g [set y | t < y] = partial_function_common_domain D f `&`
    (\bigcup_(j in D) partial_function_preimage (f j) [set y | t < y]).
Proof.
apply/seteqP; split=> x.
- move=> [y [hy hty]]; split.
  + rewrite -(partial_function_supremum_domain hg); by exists y.
  + have [z [hz htz]] : exists z, partial_function_family_values D f x z /\ t < z.
      apply: contrapT=> hn.
      have hyt : y <= t.
        apply: (@partial_function_supremum_least R X J D f g hg x y hy t)=> z hz.
        rewrite leNgt; apply/negP=> htz; apply: hn; by exists z.
      have hbad := lt_le_trans hty hyt; by rewrite ltxx in hbad.
    have [j [hj hjz]] := hz; exists j=> //; by exists z.
- move=> [hx [j hj [z [hz htz]]]].
  have [y hy] : partial_function_domain g x by rewrite (partial_function_supremum_domain hg).
  exists y; split=> //.
  have hzv : partial_function_family_values D f x z by exists j.
  exact: lt_le_trans htz (@partial_function_supremum_upper R X J D f g hg x y hy z hzv).
Qed.

(** Source for [measurable_countable_supremum]: direct supremum assertion in
    Federer 2.3.2, p. 74 The supremum is specified abstractly; empty
    families give the constant minus infinity function on the entire source. *)
Theorem measurable_countable_supremum (R : realType) (X J : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu) (D : set J)
    (f : J -> partial_function X (extended_real_line R))
    (g : partial_function X (extended_real_line R)) :
  countable D -> (forall j, D j -> is_measure_measurable_function mu (f j)) ->
  is_partial_function_supremum D f g -> is_measure_measurable_function mu g.
Proof.
move=> hc hf hg.
have hd : measure_almost_everywhere mu (partial_function_domain g).
  rewrite (partial_function_supremum_domain hg).
  apply: (@measure_almost_everywhere_countable R X J mu hm D _ hc)=> j hj.
  exact: measurable_function_domain (hf j hj).
have hD := @conull_partial_function_domain_measurable R X _ mu hm g hd.
apply: (proj2 (@measurable_extended_rational_upper_rays_iff R X mu hm g hd))=> q.
rewrite (@partial_supremum_strict_upper_preimage R X J D f g hg (ratr q : R)%:E).
apply: (@measure_measurable_intersection R X mu hm).
- by rewrite -(partial_function_supremum_domain hg).
- apply: (@measure_measurable_countable_union R X J mu hm D _ hc)=> j hj.
  apply: (@measurable_function_open_preimage R X (extended_real_line R) mu (f j) (hf j hj)).
  exact: order_strict_upper_ray_open.
Qed.

(** Source for [measurable_sealed_countable_supremum]: direct
    usable upper-envelope form of Federer 2.3.2, p. 74,
    combining abstract measurability with sealed existence. *)
Corollary measurable_sealed_countable_supremum (R : realType) (X J : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu) (D : set J)
    (f : J -> partial_function X (extended_real_line R)) :
  countable D -> (forall j, D j -> is_measure_measurable_function mu (f j)) ->
  is_measure_measurable_function mu (@PartialFunctionSupremum.value R X J D f).
Proof.
move=> hc hf; exact: (@measurable_countable_supremum R X J mu hm D f _ hc hf
  (@PartialFunctionSupremum.laws R X J D f)).
Qed.
