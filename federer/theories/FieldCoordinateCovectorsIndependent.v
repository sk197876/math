(** Federer (1969), 3.4.12, p. 339, extending 3.4.8(11), p. 333:
    the coordinate equations define the
    zero-dimensional functional stratum. Their differentials
    are the original independent coordinate covectors.
    Reuse the biorthogonal independence theorem 1.4.3. *)
From mathcomp Require Import all_boot all_order all_algebra boolp reals.
From Federer Require Import Hom TensorUP FiniteIndependence GrassmannAbbreviations FiniteCoordinates
  FieldScalarCoordinateMaps.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [field_coordinate_covectors_independent]:
    independence of the actual coordinate
    differentials for the point stratum,
    3.4.12, p. 339, extending 3.4.8(11), p. 333. *)
Lemma field_coordinate_covectors_independent (R:fieldType) n:
  finite_independent (fun i:'I_n=>@field_scalar_coordinate_map R n i).
Proof.
pose X:=coordinate_space R n.
pose test i:=@HomMap R (Hom X R^o) R^o (fun L=>L (@coordinate_basis R n i))
  (introT (asboolP _) (@hom_eval_linear R X R^o (@coordinate_basis R n i))).
apply:(@finite_independent_separating R 'I_n (Hom X R^o)
  (fun i=>@field_scalar_coordinate_map R n i)
  (fun i=>hom_as_linear (test i))).
move=>i j;change ((@coordinate_basis R n i) j = if i==j then 1 else 0).
by rewrite /coordinate_basis ffunE eq_sym.
Qed.
