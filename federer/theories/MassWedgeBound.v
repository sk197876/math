(** Federer (1969), 1.8.1, p. 39: mass is submultiplicative for exterior
    products. The proof multiplies optimal simple decompositions. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import InnerProductUP ExteriorGrading ExteriorNorm
  ExteriorAlgebra FiniteExteriorPowers ExteriorHomogeneousProducts
  AlternatingCoordinates LinearBasis AssociatedSubspace CovectorSimpleProducts SimpleWedgeNorm
  ComassUP MassUP MassOptimalDecomposition MassDecompositionBound Bilinear.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [mass_wedge_bound]: Federer 1.8.1, p. 39,
    first exterior-product inequality: mass(x wedge y) <= mass(x) mass(y).
    The positive-degree convention is explained in ComassZeroDegree.v. *)
Theorem mass_wedge_bound (R : realType) (h2 : (1+1 : R) != 0)
    (V : lmodType R) (B : V -> V -> R) (hB : is_inner_product B)
    n (e : 'I_n -> V) (he : is_basis e) p q
    (hp : (0 < p)%N) (hq : (0 < q)%N)
    (kp : A_m V R^o p -> R) (kq : A_m V R^o q -> R)
    (kr : A_m V R^o (p+q) -> R)
    (hkp : forall phi, is_comass h2 hB phi (kp phi))
    (hkq : forall phi, is_comass h2 hB phi (kq phi))
    (hkr : forall phi, is_comass h2 hB phi (kr phi))
    (x : exterior_power V p) (y : exterior_power V q) a b c :
  is_mass kp x a -> is_mass kq y b ->
  is_mass kr (exterior_product x y) c -> c <= a*b.
Proof.
move=> ha hb hc.
have [j [u [hjd [hu [hxu hau]]]] ] :=
  @mass_optimal_simple_decomposition R h2 V B hB n e he p hp kp hkp x a ha.
have [k [v [hkd [hv [hyv hbv]]]] ] :=
  @mass_optimal_simple_decomposition R h2 V B hB n e he q hq kq hkq y b hb.
pose w (ij : 'I_j * 'I_k) := exterior_product (u ij.1) (v ij.2).
have hw ij : simple (w ij) := simple_exterior_product (hu ij.1) (hv ij.2).
have hex : exterior_product x y = \sum_ij w ij.
  rewrite hxu hyv.
  rewrite (big_morph (fun z => exterior_product z (\sum_i v i))
    (fun z t => bilDl (@exterior_product_bilinear R V p q) z t (\sum_i v i))
    (bil0l (@exterior_product_bilinear R V p q) (\sum_i v i))).
  under eq_bigr do rewrite (big_morph (fun z => exterior_product _ z)
    (bilDr (@exterior_product_bilinear R V p q) _) (bil0r (@exterior_product_bilinear R V p q) _)).
  by rewrite pair_big.
have hpq : (0 < p+q)%N := leq_trans hp (leq_addr q p).
have hc' : is_mass kr (\sum_ij w ij) c by rewrite -hex.
have hh := @simple_decomposition_mass_bound R h2 V B hB (p+q) hpq kr hkr
  (Finite.clone ('I_j * 'I_k)%type _) w c hw hc'.
have hsum : a*b = \sum_ij exterior_norm h2 hB (u ij.1) * exterior_norm h2 hB (v ij.2).
  rewrite hau hbv mulr_suml.
  under eq_bigr do rewrite mulr_sumr.
  by rewrite pair_big.
apply: (le_trans hh); rewrite hsum; apply: ler_sum => ij _.
exact: simple_right_wedge_norm_bound (hv ij.2).
Qed.
