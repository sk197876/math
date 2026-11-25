(** Federer (1969), 2.7.1, printed p. 122: "A^x induces a homeomorphism
    G/G^x ~ X, which maps each coset g G^x onto A(g,x)." The map A^x is
    constant on the cosets of the isotropy subgroup G^x, so it factors
    through the projection G -> G/G^x; the factor is injective because
    A(g,x) = A(h,x) holds only when g^{-1} h is in G^x, onto because im A^x
    = X, continuous by the quotient topology, and open because A^x is open.
    The result holds for every space with the specification of G/G^x of
    CosetSpaceUP.v, in particular for the sealed coset space of
    CosetSpace.v. Only the group laws and the conditions defining a
    homogeneous space are used. *)
From mathcomp Require Import all_boot boolp classical_sets topology.
From Federer Require Import HomeomorphismUP TopologicalGroupUP TopologicalGroupLaws
  HomogeneousSpaceUP HomogeneousSpaceLaws CosetSpaceUP CosetSpaceLaws CosetSpace.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

Section IsotropyQuotient.
Variables G X Q : topologicalType.
Variables (mul : G -> G -> G) (inv : G -> G) (e : G) (A : G -> X -> X) (x : X) (pi : G -> Q).
Hypothesis hG : is_group_laws mul inv e.
Hypothesis hA : is_homogeneous_space mul A.
Hypothesis hQ : is_left_coset_space mul inv (isotropy_subgroup A x) pi.

(** Source for [isotropy_quotient_homeomorphism]: "A^x induces a
    homeomorphism G/G^x ~ X, which maps each coset g G^x onto A(g,x)",
    Federer 2.7.1, p. 122, for any space Q with projection pi
    specified as G/G^x. Direct formalisation, with the uniqueness of the
    induced map added. *)
Theorem isotropy_quotient_homeomorphism :
  exists phi : Q -> X, [/\ forall g, phi (pi g) = A g x, is_homeomorphism phi &
    forall psi : Q -> X, (forall g, psi (pi g) = A g x) -> psi = phi].
Proof.
have hconst : forall g h, isotropy_subgroup A x (mul (inv g) h) -> orbit_map A x g = orbit_map A x h.
  by move=> g h /(orbit_map_eq hG hA).
have [phi hphi] := coset_space_factor hQ hconst.
have hcomp : phi \o pi = orbit_map A x by apply: funext=> g; exact: hphi.
exists phi; split=> //.
- apply: open_continuous_bijection_homeomorphism.
  + by apply/(coset_space_factor_continuous hQ); rewrite hcomp; exact: orbit_map_continuous hA x.
  + move=> U hU.
    have -> : phi @` U = orbit_map A x @` (pi @^-1` U).
      apply/seteqP; split=> y.
      * case=> q hq <-; have [g hg] := coset_projection_onto hQ q.
        by exists g; [rewrite /= hg|rewrite -hg hphi].
      * by case=> g hg <-; exists (pi g)=> //; exact: hphi.
    by apply: homogeneous_orbit_open hA x _ _; apply/(coset_space_open hQ).
  + move=> q1 q2; have [g <-] := coset_projection_onto hQ q1.
    have [h <-] := coset_projection_onto hQ q2.
    rewrite !hphi /orbit_map=> /(orbit_map_eq hG hA) hgh.
    exact/(coset_projection_eq hQ).
  + by move=> y; have [g hg] := homogeneous_transitive hA x y; exists (pi g); rewrite hphi.
- by move=> psi hpsi; apply: (coset_space_factor_unique hQ)=> g; rewrite hpsi hphi.
Qed.

End IsotropyQuotient.

(** Source for [isotropy_coset_space_homeomorphism]: "A^x induces a
    homeomorphism G/G^x ~ X, which maps each coset g G^x onto A(g,x)",
    Federer 2.7.1, p. 122, for the sealed coset space G/G^x of
    CosetSpace.v. Direct formalisation. *)
Theorem isotropy_coset_space_homeomorphism (G X : topologicalType) (mul : G -> G -> G)
    (inv : G -> G) (e : G) (A : G -> X -> X) (x : X) :
  is_group_laws mul inv e -> is_homogeneous_space mul A ->
  exists phi : coset_space mul (isotropy_subgroup A x) -> X,
    [/\ forall g, phi (coset_projection mul (isotropy_subgroup A x) g) = A g x &
      is_homeomorphism phi].
Proof.
move=> hG hA.
have hS := isotropy_subgroup_subgroup hG hA x.
have hQ := coset_space_specification hG hS.
have [phi [hphi hh _]] := isotropy_quotient_homeomorphism hG hA hQ.
by exists phi.
Qed.
