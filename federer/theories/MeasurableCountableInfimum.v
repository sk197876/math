(** Federer (1969), 2.3.2, p. 74: measurability of countable pointwise
    infima of extended-real partial functions. The proof uses abstract
    greatest-lower-bound laws and rational lower rays. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  cardinality reals constructive_ereal topology.
From Federer Require Import PartialFunctionUP PartialFunctionSupremumUP PartialFunctionInfimumUP
  PartialFunctionInfimumSealed ExtendedRealOrderTopology CountableOrderIntervals MeasureUP MeasureAlmostUP
  MeasureAlmostBasic MeasureFiniteClosure MeasureCountableClosure MeasurableFunctionUP
  MeasurableFunctionBorel MeasurableExtendedRationalRays.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [partial_infimum_strict_lower_preimage]: supporting
    lower-ray formula for the infimum in Federer 2.3.2, p. 74.
    The common domain remains explicit, including empty families. *)
Lemma partial_infimum_strict_lower_preimage (R : realType) (X J : Type) (D : set J)
    (f : J -> partial_function X (extended_real_line R))
    (g : partial_function X (extended_real_line R)) (hg : is_partial_function_infimum D f g)
    (t : \bar R) :
  partial_function_preimage g [set y | y < t] = partial_function_common_domain D f `&`
    (\bigcup_(j in D) partial_function_preimage (f j) [set y | y < t]).
Proof.
apply/seteqP; split=> x.
- move=> [y [hy hyt]]; split.
  + rewrite -(partial_function_infimum_domain hg); by exists y.
  + have [z [hz hzt]] : exists z, partial_function_family_values D f x z /\ z < t.
      apply: contrapT=> hn.
      have hty : t <= y.
        apply: (@partial_function_infimum_greatest R X J D f g hg x y hy t)=> z hz.
        rewrite leNgt; apply/negP=> hzt; apply: hn; by exists z.
      have hbad := lt_le_trans hyt hty; by rewrite ltxx in hbad.
    have [j [hj hjz]] := hz; exists j=> //; by exists z.
- move=> [hx [j hj [z [hz hzt]]]].
  have [y hy] : partial_function_domain g x by rewrite (partial_function_infimum_domain hg).
  exists y; split=> //.
  have hzv : partial_function_family_values D f x z by exists j.
  exact: le_lt_trans (@partial_function_infimum_lower R X J D f g hg x y hy z hzv) hzt.
Qed.

(** Source for [measurable_countable_infimum]: direct infimum assertion in
    Federer 2.3.2, p. 74 Empty families give the constant plus infinity
    function on the entire source. *)
Theorem measurable_countable_infimum (R : realType) (X J : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu) (D : set J)
    (f : J -> partial_function X (extended_real_line R))
    (g : partial_function X (extended_real_line R)) :
  countable D -> (forall j, D j -> is_measure_measurable_function mu (f j)) ->
  is_partial_function_infimum D f g -> is_measure_measurable_function mu g.
Proof.
move=> hc hf hg.
have hd : measure_almost_everywhere mu (partial_function_domain g).
  rewrite (partial_function_infimum_domain hg).
  apply: (@measure_almost_everywhere_countable R X J mu hm D _ hc)=> j hj.
  exact: measurable_function_domain (hf j hj).
have hD := @conull_partial_function_domain_measurable R X _ mu hm g hd.
apply: (proj2 (@measurable_extended_rational_lower_rays_iff R X mu hm g hd))=> q.
rewrite (@partial_infimum_strict_lower_preimage R X J D f g hg (ratr q : R)%:E).
apply: (@measure_measurable_intersection R X mu hm).
- by rewrite -(partial_function_infimum_domain hg).
- apply: (@measure_measurable_countable_union R X J mu hm D _ hc)=> j hj.
  apply: (@measurable_function_open_preimage R X (extended_real_line R) mu (f j) (hf j hj)).
  exact: order_strict_lower_ray_open.
Qed.

(** Source for [measurable_sealed_countable_infimum]: direct
    usable lower-envelope form of Federer 2.3.2, p. 74,
    combining abstract measurability and sealed existence. *)
Corollary measurable_sealed_countable_infimum (R : realType) (X J : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu) (D : set J)
    (f : J -> partial_function X (extended_real_line R)) :
  countable D -> (forall j, D j -> is_measure_measurable_function mu (f j)) ->
  is_measure_measurable_function mu (@PartialFunctionInfimum.value R X J D f).
Proof.
move=> hc hf; exact: (@measurable_countable_infimum R X J mu hm D f _ hc hf
  (@PartialFunctionInfimum.laws R X J D f)).
Qed.
