(** Federer (1969), 3.2.48, pp. 285–286: the actual
    tangent profile on countably many sphere-contained manifold pieces.
    Piece labels depend only on the unchanged base points. Local
    partition selectors are supplied by proved set-theoretic laws. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets.
From Federer Require Import Hom GrassmannAbbreviations EuclideanInnerProduct
  DisjointFamilySelector SphericalKinematicTangentProfile.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [spherical_kinematic_partition_profile]: supporting
    piecewise representative of the actual tangent Jacobian in
    3.2.48, pp. 285–286. This defines no orientation or tangent
    frame field. The manifold and selector laws, followed by their
    existence and the approximate-graph theorem, justify its use. *)
Definition spherical_kinematic_partition_profile (R:realType) d n v
    (c:R_n R (1+d)) (M N:set (R_n R (1+d))->set (R_n R (1+d)))
    (sA sB:R_n R (1+d)->set (R_n R (1+d)))
    (e:Hom (R_n R n) [the lmodType R of
      ((Hom (R_n R (1+d)) (R_n R (1+d)))*(Hom (R_n R (1+d)) (R_n R (1+d))))%type])
    (p:Hom [the lmodType R of
      ((Hom (R_n R (1+d)) (R_n R (1+d)))*(Hom (R_n R (1+d)) (R_n R (1+d))))%type] (R_n R n))
    (t:Hom (Hom (R_n R (1+d)) (R_n R (1+d))) (R_n R v))
    (z:Hom (R_n R (1+d)) (R_n R (1+d))*Hom (R_n R (1+d)) (R_n R (1+d))):=
  spherical_kinematic_tangent_profile c (M (sA (z.1 c))) (N (sB (z.2 c))) e p t z.

(** Source for [spherical_kinematic_partition_profile_on]: the
    original manifold profile on each actual partition piece,
    3.2.48, p. 285. Disjointness gives exact selector values;
    no measurability or choice of tangent words is assumed. *)
Lemma spherical_kinematic_partition_profile_on (R:realType) d n v
    (c:R_n R (1+d)) (M N:set (R_n R (1+d))->set (R_n R (1+d)))
    (P Q:set (set (R_n R (1+d)))) (sA sB:R_n R (1+d)->set (R_n R (1+d)))
    (e:Hom (R_n R n) [the lmodType R of
      ((Hom (R_n R (1+d)) (R_n R (1+d)))*(Hom (R_n R (1+d)) (R_n R (1+d))))%type])
    (p:Hom [the lmodType R of
      ((Hom (R_n R (1+d)) (R_n R (1+d)))*(Hom (R_n R (1+d)) (R_n R (1+d))))%type] (R_n R n))
    (t:Hom (Hom (R_n R (1+d)) (R_n R (1+d))) (R_n R v))
    (z:Hom (R_n R (1+d)) (R_n R (1+d))*Hom (R_n R (1+d)) (R_n R (1+d))) E F:
  is_disjoint_family_selector P sA ->is_disjoint_family_selector Q sB ->
  P E ->Q F ->E (z.1 c) ->F (z.2 c) ->
  spherical_kinematic_partition_profile c M N sA sB e p t z=
    spherical_kinematic_tangent_profile c (M E) (N F) e p t z.
Proof.
move=>hA hB hE hF hx hy.
by rewrite /spherical_kinematic_partition_profile (hA E hE _ hx) (hB F hF _ hy).
Qed.
