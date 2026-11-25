(** Federer (1969), 4.1.27, p. 384: opaque
    access to the original prefix-product cube
    map. Its independent pointwise formula is
    exposed; the finite-sum existence witness stays
    hidden behind the module signature. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct
  SimplexCubeParametrisationUP SimplexCubeParametrisationExistence.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module Type SimplexCubeParametrisationSignature.
(** Source for [value]: the original map f
    in 4.1.27, p. 384. *)
Parameter value:forall (R:realType) n m,
  ('I_(m.+1)->R_n R n)->R_n R m->R_n R n.
(** Source for [laws]: exactly the original coordinate
    formula, 4.1.27, p. 384. *)
Parameter laws:forall (R:realType) n m (v:'I_(m.+1)->R_n R n),
  @is_simplex_cube_parametrisation R n m v (@value R n m v).
End SimplexCubeParametrisationSignature.

Module SimplexCubeParametrisation:SimplexCubeParametrisationSignature.
(** Source for [value]: select only the previously
    proved map witness of 4.1.27, p. 384. *)
Definition value (R:realType) n m (v:'I_(m.+1)->R_n R n):=
  projT1 (cid (@simplex_cube_parametrisation_exists R n m v)).
(** Source for [laws]: the hidden witness has
    the independent printed formula, 4.1.27,
    p. 384. *)
Lemma laws (R:realType) n m (v:'I_(m.+1)->R_n R n):
  @is_simplex_cube_parametrisation R n m v (@value R n m v).
Proof. exact:projT2 (cid (@simplex_cube_parametrisation_exists R n m v)). Qed.
End SimplexCubeParametrisation.

Arguments SimplexCubeParametrisation.value : clear implicits.
Arguments SimplexCubeParametrisation.laws : clear implicits.
