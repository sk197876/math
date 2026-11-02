(** Federer (1969), 2.10.41, printed p. 200: the minimum centre belongs to
    the convex hull of contact points on its radius-c sphere. Translate the
    centre to zero and apply the finite contact representation and weighted
    distance calculation. *)
From mathcomp Require Import all_boot all_order all_algebra reals classical_sets.
From Federer Require Import LinearBasis InnerProductUP InnerNorm ConvexHull
  ConvexHullFiniteSupport JungWeightedDistances JungConstant.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [inner_hull_sphere_jung_bound]: direct
    contact-point calculation of 2.10.41, p. 200.
    A centre in the convex hull of points on its
    radius-c sphere satisfies 2c<=sqrt(2n/(n+1)) d
    whenever those points have pairwise distance at most d.
    The supporting statement is intrinsic to any real
    inner-product space with a specified n-element basis. *)
Theorem inner_hull_sphere_jung_bound (R : realType) (V : lmodType R)
    (B : V -> V -> R) (hB : is_inner_product B) n (e : 'I_n -> V)
    (A : set V) (b : V) (c d : R) :
  is_basis e -> A !=set0 -> convex_hull A b -> 0<=c -> 0<=d ->
  (forall a, A a -> inner_norm hB (a-b)=c) ->
  (forall a a', A a -> A a' -> inner_norm hB (a-a')<=d) ->
  c+c<=@jung_factor R n*d.
Proof.
move=> he hne hb hc hd hsphere hdiam.
have [k [u [w [hk [hu [hw [hsum hvalue]]]]]]] :=
  @convex_hull_finite_support R V n e A b he hne hb.
pose v i := u i-b.
have hv i : inner_norm hB (v i)=c := hsphere _ (hu i).
have hmean : \sum_i w i*:v i=0.
  rewrite /v; under eq_bigr do rewrite scalerBr.
  by rewrite sumrB -scaler_suml hsum scale1r -hvalue subrr.
have hdistance i j : inner_norm hB (v i-v j)<=d.
  have heq : v i-v j=u i-u j by rewrite /v opprB addrA subrK.
  rewrite heq; exact: hdiam _ _ (hu i) (hu j).
have hcount := @inner_convex_spherical_jung_count R V B hB k v w c d
  hd hw hsum hmean hv hdistance.
exact (@jung_contact_count_diameter_bound R n k c d hk hc hd hcount).
Qed.
