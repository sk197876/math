(** Federer (1969), 1.8.4, pp. 40-41: multiplicativity
    of mass for orthogonally supported factors when the first is
    simple. Finite ambient dimension is the standing hypothesis
    of 1.8.1, p. 38. Subspaces are arbitrary specified subspaces;
    no coordinate construction of them is assumed. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import SimpleVectors SimpleElementary SimpleOrthonormalFactor
  SubspaceCarrier InnerProductUP InnerProductRestriction OrthonormalFamilies
  ExteriorGrading ExteriorMaps ExteriorNorm ExteriorNormNaturality
  ExteriorHomogeneousProducts CovectorProductNaturality AlternatingCoordinates
  ComassUP MassUP MassBounds MassSealed MassHomogeneity MassEquality
  OrthogonalBlockMass LinearBasis.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [orthogonal_simple_left_mass]: Federer 1.8.4,
    pp. 40-41, the mass product equation when xi is simple,
    with xi and eta in the images of the exterior inclusion maps
    of mutually orthogonal subspaces. Zero factors are included. *)
Theorem orthogonal_simple_left_mass (R : realType) (h2 : (1+1 : R) != 0)
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
  simple (exterior_power_map (subspace_inclusion S) p x0) ->
  is_mass kp (exterior_power_map (subspace_inclusion S) p x0) a ->
  is_mass kq (exterior_power_map (subspace_inclusion T) q y0) b ->
  is_mass kr (exterior_product (exterior_power_map (subspace_inclusion S) p x0)
    (exterior_power_map (subspace_inclusion T) q y0)) c -> c=a*b.
Proof.
move=> hx ha hb hc.
pose x := exterior_power_map (subspace_inclusion S) p x0.
pose y := exterior_power_map (subspace_inclusion T) q y0.
have hpq : (0 < p+q)%N := leq_trans hp (leq_addr q p).
case hx0 : (x == 0).
- move/eqP: hx0=> hz.
  have ha0 : a=0.
    apply: mass_unique (@mass_zero R h2 V B hB p hp kp hkp).
    by rewrite -hz.
  have hc0 : c=0.
    apply: mass_unique (@mass_zero R h2 V B hB (p+q) hpq kr hkr).
    by move: hc; rewrite -/x hz (bil0l (@exterior_product_bilinear R V p q)).
  by rewrite ha0 hc0 mul0r.
- have hxn : x != 0 by rewrite hx0.
  have hx0n : x0 != 0.
    apply/eqP=> hz; move: hxn; by rewrite /x hz linear0 eqxx.
  have hs0 : simple x0.
    have hh := exterior_power_map_simple (subspace_retraction S) hx.
    rewrite (@exterior_power_mapK R (GRing.Lmodule.clone R (subspace_space S) _) V
      (subspace_inclusion S) (subspace_retraction S) (@subspace_retractionK R V S) p) in hh.
    exact hh.
  pose U := GRing.Lmodule.clone R (subspace_space S) _.
  pose C := @restricted_inner_product R V B S.
  pose hC := restricted_inner_productP hB S.
  have [u [t [hu [ht hxu]]]] := @simple_orthonormal_factor R h2 U C hC p x0 hx0n hs0.
  pose v := fun i => subspace_inclusion S (u i).
  have hv : orthonormal_family B v by move=> i j; exact: hu.
  have hxy : x = t *: e_lambda v (ord_tuple p).
    by rewrite /x hxu linearZ exterior_basis_product_natural.
  have hvt i w : B (v i) (subspace_inclusion T w) = 0.
    apply: hST; exact: subspace_valP.
  have haN := @simple_mass_euclidean R h2 V B hB n e he p hp kp hkp x a hx ha.
  have hat : a = `|t|.
    by rewrite hxy exterior_norm_scale (orthonormal_product_unit_norm h2 hB hv) mulr1 in haN.
  pose z := exterior_product (e_lambda v (ord_tuple p)) y.
  pose d := @MassSealed.Mass.norm R h2 V B hB n e he (p+q) hpq kr hkr z.
  have hd : is_mass kr z d := @MassSealed.Mass.laws R h2 V B hB n e he (p+q) hpq kr hkr z.
  have hdb : d=b := @orthonormal_block_mass R h2
    (GRing.Lmodule.clone R (subspace_space T) _) V B hB n e he p q hp hq
    kp kq kr hkp hkq hkr v hv (subspace_inclusion T) hvt y0 b d hb hd.
  have hct : is_mass kr (t *: z) c.
    move: hc; by rewrite -/x hxy (bilZl (@exterior_product_bilinear R V p q)).
  have hh := @mass_absolute_homogeneity R h2 V B hB (p+q) hpq kr hkr z t d c hd hct.
  by rewrite hdb -hat in hh.
Qed.
