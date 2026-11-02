(** Federer (1969), 2.4.10, p. 85: multiplying a nonnegative characteristic
    series by a nonnegative density commutes with summation, including zero
    times infinity. This supporting version handles a nonempty arbitrary
    index set with total summands and a possibly partial density. Source
    editions: PartialZeroExtensionUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import ExtendedRealOrderTopology PartialFunctionUP PartialFunctionBasic PartialDensityProduct
  PartialNumericalSumUP NumericalSum NumericalSumValues NonnegativeSum NonnegativeSumSupport NonnegativeSumExtendedScale.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [partial_density_total_series]: exact graph identity for the
    multiplied characteristic expansion in Federer 2.4.10, p. 85
    Nonemptiness ensures that the sum retains precisely the density domain,
    also where the target sum is zero. *)
Lemma partial_density_total_series (R : realType) (X : Type) (J : choiceType)
    (D : set J) (u : J -> X -> extended_real_line R) (f : X -> extended_real_line R)
    (h : partial_function X (extended_real_line R)) :
  (exists j, D j) -> (forall j, D j -> forall x, 0 <= u j x) ->
  (forall x z, partial_function_graph h x z -> 0 <= z) ->
  (forall x, nonnegative_sum D (fun j => u j x)=f x) ->
  is_partial_function_numerical_sum D
    (fun j => partial_density_product (partial_function_total (u j)) h)
    (partial_density_product (partial_function_total f) h).
Proof.
move=> [j0 hj0] hp hh hsum x z; split.
- move=> hz; have [a [b [ha [hb hab]]]] := (partial_density_product_graph _ h x z).1 hz.
  exists (fun j => u j x*b); split.
  + move=> j hj; apply/partial_density_product_graph; exists (u j x),b; by split=> //; split.
  + have hprod j : D j -> 0 <= u j x*b by move=> hj; exact: mule_ge0 (hp j hj x) (hh x b hb).
    rewrite (numerical_sum_nonnegative hprod).
    have he : nonnegative_sum D (fun j => u j x*b) = b*nonnegative_sum D (fun j => u j x).
      rewrite -(@nonnegative_sum_extended_scale R J D (fun j => u j x) b (hh x b hb) (fun j hj => hp j hj x)).
      apply: nonnegative_sum_ext=> j hj; exact: muleC.
    by rewrite he hsum muleC (ha : f x=a) hab.
- move=> [v [hv hvsum]].
  have [a0 [b [ha0 [hb he0]]]] := (partial_density_product_graph _ h x (v j0)).1 (hv j0 hj0).
  have he j (hj : D j) : v j=u j x*b.
    have [a [c [ha [hc hac]]]] := (partial_density_product_graph _ h x (v j)).1 (hv j hj).
    have ebc := partial_function_single_valued hb hc.
    by rewrite -(ha : u j x=a) -ebc in hac; symmetry.
  have hprod j : D j -> 0 <= u j x*b by move=> hj; exact: mule_ge0 (hp j hj x) (hh x b hb).
  have hev : numerical_sum D v = numerical_sum D (fun j => u j x*b).
    apply: numerical_sum_ext; exact he.
  rewrite hev (numerical_sum_nonnegative hprod) in hvsum.
  have hscale : nonnegative_sum D (fun j => u j x*b)=f x*b.
    rewrite muleC -hsum -(@nonnegative_sum_extended_scale R J D (fun j => u j x) b
      (hh x b hb) (fun j hj => hp j hj x)).
    apply: nonnegative_sum_ext=> j hj; exact: muleC.
  rewrite hscale in hvsum; case: hvsum=> ez.
  apply/partial_density_product_graph; exists (f x),b; by split=> //; split.
Qed.

(** Source for [partial_total_nonnegative_series]: supporting
    graph form of the characteristic expansion in Federer
    2.4.10, p. 85, before multiplying by the density. *)
Lemma partial_total_nonnegative_series (R : realType) (X : Type) (J : choiceType)
    (D : set J) (u : J -> X -> extended_real_line R) (f : X -> extended_real_line R) :
  (forall j, D j -> forall x, 0 <= u j x) ->
  (forall x, nonnegative_sum D (fun j => u j x)=f x) ->
  is_partial_function_numerical_sum D (fun j => partial_function_total (u j)) (partial_function_total f).
Proof.
move=> hp he x z; split.
- move=> hz; exists (fun j => u j x); split=> //.
  rewrite (numerical_sum_nonnegative (fun j hj => hp j hj x)) he; by rewrite (hz : f x=z).
- move=> [v [hv hs]].
  have hev : numerical_sum D v=numerical_sum D (fun j => u j x).
    apply: numerical_sum_ext=> j hj; symmetry; exact: hv j hj.
  rewrite hev (numerical_sum_nonnegative (fun j hj => hp j hj x)) he in hs.
  by case: hs.
Qed.
