(** Federer (1969), 1.8.4, pp. 40-41: the full mass
    product equation for orthogonally supported factors when either
    is simple. The final sentence of the item asks about the case
    where neither is simple; no such general assertion is made here.
    Positive degrees follow the explicit norm convention of 1.8.1. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import SimpleVectors SubspaceCarrier InnerProductUP
  ExteriorGrading ExteriorMaps ExteriorHomogeneousProducts AlternatingCoordinates
  ComassUP ComassSealed MassUP MassSealed MassWedgeSymmetry OrthogonalSimpleMass LinearBasis.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [orthogonal_mass_product]: Federer 1.8.4,
    pp. 40-41, the displayed mass equation with either simple
    factor. Both factors are actual images under the specified
    exterior inclusion maps of the mutually orthogonal subspaces. *)
Theorem orthogonal_mass_product (R : realType) (h2 : (1+1 : R) != 0)
    (V : lmodType R) (B : V -> V -> R) (hB : is_inner_product B)
    n (e : 'I_n -> V) (he : is_basis e) (S T : subspace V)
    (hST : forall u v, S u -> T v -> B u v = 0)
    p q (hp : (0 < p)%N) (hq : (0 < q)%N)
    (kp : A_m V R^o p -> R) (kq : A_m V R^o q -> R)
    (kr : A_m V R^o (p+q) -> R)
    (hkp : forall phi, is_comass h2 hB phi (kp phi))
    (hkq : forall phi, is_comass h2 hB phi (kq phi))
    (hkr : forall phi, is_comass h2 hB phi (kr phi))
    (x0 : exterior_power (subspace_space S) p)
    (y0 : exterior_power (subspace_space T) q) a b c :
  (simple (exterior_power_map (subspace_inclusion S) p x0) \/
    simple (exterior_power_map (subspace_inclusion T) q y0)) ->
  is_mass kp (exterior_power_map (subspace_inclusion S) p x0) a ->
  is_mass kq (exterior_power_map (subspace_inclusion T) q y0) b ->
  is_mass kr (exterior_product (exterior_power_map (subspace_inclusion S) p x0)
    (exterior_power_map (subspace_inclusion T) q y0)) c -> c=a*b.
Proof.
move=> hs ha hb hc; case: hs=> [hx|hy].
- exact: (@orthogonal_simple_left_mass R h2 V B hB n e he S T hST
    p q hp hq kp kq kr hkp hkq hkr x0 y0 a b c hx ha hb hc).
- have hqp : (0 < q+p)%N := leq_trans hq (leq_addr p q).
  pose ks := @ComassSealed.Comass.norm R h2 V B hB n e he (q+p) hqp.
  have hks phi : is_comass h2 hB phi (ks phi) :=
    @ComassSealed.Comass.laws R h2 V B hB n e he (q+p) hqp phi.
  pose x := exterior_power_map (subspace_inclusion S) p x0.
  pose y := exterior_power_map (subspace_inclusion T) q y0.
  pose d := @MassSealed.Mass.norm R h2 V B hB n e he (q+p) hqp ks hks (exterior_product y x).
  have hd : is_mass ks (exterior_product y x) d :=
    @MassSealed.Mass.laws R h2 V B hB n e he (q+p) hqp ks hks (exterior_product y x).
  have hTS u v : T u -> S v -> B u v=0.
    move=> hu hv; rewrite (inner_symmetric hB); exact: hST hv hu.
  have hdb := @orthogonal_simple_left_mass R h2 V B hB n e he T S hTS
    q p hq hp kq kp ks hkq hkp hks y0 x0 b a d hy hb ha hd.
  have hcd := @mass_wedge_swap R h2 V B hB p q
    (leq_trans hp (leq_addr q p)) kr ks hkr hks x y c d hc hd.
  by rewrite hcd hdb mulrC.
Qed.
