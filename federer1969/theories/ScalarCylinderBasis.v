(** Federer (1969), 3.2.33, p. 270: the first mu
    orthonormal directions are preserved by the actual differential. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp.
From Federer Require Import Hom GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct
  ScalarCylinderMapUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [scalar_cylinder_first_basis_image]: the
    identity first block of Df, supporting J_mu f>= 1
    in Federer 3.2.33, p. 270. The scalar derivative
    may vanish; no positive-rank assumption is required. *)
Lemma scalar_cylinder_first_basis_image (R:realType) mu k c
    (L:Hom (R_n R ((mu+1)+k)) (R_n R (mu+1))):
  is_scalar_cylinder_map (fun t=>c*t) L ->forall i:'I_mu,
    L (@coordinate_basis R ((mu+1)+k) (lshift k (lshift 1 i)))=
      @coordinate_basis R (mu+1) (lshift 1 i).
Proof.
move=>hL i; apply/ffunP=>j; rewrite -(splitK j); case:(split j)=>a.
- by rewrite (scalar_cylinder_first_coordinates hL) /coordinate_basis !ffunE
    (inj_eq (@lshift_inj (mu+1) k)).
- by rewrite (ord1 a) (scalar_cylinder_last_coordinate hL) /coordinate_basis !ffunE
    (inj_eq (@lshift_inj (mu+1) k)) !eq_rlshift mulr0.
Qed.
