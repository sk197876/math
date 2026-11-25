(** Federer (1969), 4.1.7, p. 356: contraction
    by a fixed one-covector in the original
    divergence identity. The earlier finite-dimensional
    norm bound supplies continuity of this actual map. *)
From mathcomp Require Import all_boot all_order all_algebra boolp reals.
From Federer Require Import Hom Bilinear RealNormUP NormDifferentialUP GrassmannAbbreviations
  ExteriorGrading AlternatingForms CurrentCoefficientNorms CurrentVectorSpaces OneCovectorInterior
  NormFiniteLinearBound.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Section CurrentOneCovectorMap.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n p:nat.
Local Notation X := (R_n R n).
Local Notation Y := (exterior_power X p.+1).
Local Notation Z := (exterior_power X p).
Local Notation NY := (@current_vector_mass R h2 n p.+1).
Local Notation NZ := (@current_vector_mass R h2 n p).
Variable alpha:A_m X R^o 1.

(** Source for [current_one_covector_map]: the original
    fixed contraction xi to xi contracted alpha,
    supporting Federer 4.1.7, p. 356. *)
Definition current_one_covector_map:Hom Y Z:=
  @HomMap R Y Z (fun xi=>positive_one_covector_interior h2 xi alpha)
    (introT (asboolP _) ((@positive_one_covector_interior_bilinear R h2 X p).1 alpha)).

(** Source for [current_one_covector_map_bounded]:
    the original contraction has a finite
    homogeneous mass bound, supporting Federer
    4.1.7, p. 356, by 1.9.1. *)
Theorem current_one_covector_map_bounded:
  norm_bounded_linear NY NZ current_one_covector_map.
Proof.
have[d [b hb]]:=@current_vector_finite_basis R h2 n p.+1.
exact:(@norm_finite_linear_bounded R Y Z NY NZ
  (@current_vector_mass_real_norm R h2 n p.+1)
  (@current_vector_mass_real_norm R h2 n p) d b hb current_one_covector_map).
Qed.
End CurrentOneCovectorMap.
