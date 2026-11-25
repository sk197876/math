(** Federer (1969), 3.4.12, p. 339, extending 3.4.8(8), p. 329:
    adjacent original prefix projections compose,
    and their actual germ pullbacks compose
    contravariantly. Apply the existing representative
    composition theorem after checking the exact
    original coordinate equations. *)
From mathcomp Require Import all_boot all_order all_algebra boolp reals.
From Federer Require Import ScalarRestriction ComplexScalarSealed ComplexNormUP FiniteCoordinates HolomorphicCoordinateNorm Hom RealNormUP GrassmannAbbreviations FiniteCoordinates
  EuclideanInnerProduct InnerNorm HilbertFormCompactness FieldCoordinateFunctional FieldAdjacentPrefixComposition
  HolomorphicGermUP FieldPrefixCoordinatesUP PointedHolomorphicPullbackUP PointedHolomorphicPullbackComposition.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [holomorphic_adjacent_prefix_composition]:
    the original p_j is the first j
    coordinates of p_(j+1), as used for
    the nested rings Q_j in 3.4.8(8),
    p. 329. Widened index proofs are
    compared through their actual ordinal values. *)
Theorem holomorphic_adjacent_prefix_composition (R:realType) (X:lmodType (ComplexScalars.C R)) n
  (omega:'I_n->Hom X (ComplexScalars.C R)^o) j (hJN:(j<=n)%N) (hJ1N:(j.+1<=n)%N)
  (P:Hom X (coordinate_space (ComplexScalars.C R) j)) (Q:Hom X (coordinate_space (ComplexScalars.C R) j.+1))
  (between:Hom (coordinate_space (ComplexScalars.C R) j.+1) (coordinate_space (ComplexScalars.C R) j)):
  is_field_prefix_projection omega hJN P ->
  is_field_prefix_projection omega hJ1N Q ->
  is_field_prefix_projection (fun i:'I_j.+1=>field_coordinate_functional i) (leqnSn j) between ->
  forall x:X,P x = between (Q x).
Proof.
exact:(@field_adjacent_prefix_composition (ComplexScalars.C R) X n omega j hJN hJ1N P Q between).
Qed.

(** Source for [holomorphic_adjacent_prefix_germ_composition]:
    O_0(p_j) factors through O_0(p_(j+1)),
    the coefficient-ring compatibility in 3.4.8(8),
    p. 329. Apply the existing pointed
    pullback composition and map-extensionality theorems;
    no representative implementation is inspected. *)
Theorem holomorphic_adjacent_prefix_germ_composition (R:realType) (X:lmodType (ComplexScalars.C R))
  (NX:X->R) (hNX:@is_real_norm R (restricted_space (ComplexScalars.embed R) X) NX) n (omega:'I_n->Hom X (ComplexScalars.C R)^o)
  j (hJN:(j<=n)%N) (hJ1N:(j.+1<=n)%N)
  (P:Hom X (coordinate_space (ComplexScalars.C R) j)) (Q:Hom X (coordinate_space (ComplexScalars.C R) j.+1))
  (between:Hom (coordinate_space (ComplexScalars.C R) j.+1) (coordinate_space (ComplexScalars.C R) j))
  (EP:holomorphic_germ_space (complex_norm_real (@holomorphic_coordinate_norm_laws R j)) (0:coordinate_space (ComplexScalars.C R) j)->
    holomorphic_germ_space hNX (0:X))
  (EQ:holomorphic_germ_space (complex_norm_real (@holomorphic_coordinate_norm_laws R j.+1)) (0:coordinate_space (ComplexScalars.C R) j.+1)->
    holomorphic_germ_space hNX (0:X))
  (EB:holomorphic_germ_space (complex_norm_real (@holomorphic_coordinate_norm_laws R j)) (0:coordinate_space (ComplexScalars.C R) j)->
    holomorphic_germ_space (complex_norm_real (@holomorphic_coordinate_norm_laws R j.+1)) (0:coordinate_space (ComplexScalars.C R) j.+1)):
  is_field_prefix_projection omega hJN P ->is_field_prefix_projection omega hJ1N Q ->
  is_field_prefix_projection (fun i:'I_j.+1=>field_coordinate_functional i) (leqnSn j) between ->
  is_pointed_holomorphic_germ_pullback P EP ->is_pointed_holomorphic_germ_pullback Q EQ ->
  is_pointed_holomorphic_germ_pullback between EB ->
  forall alpha,EP alpha = EQ (EB alpha).
Proof.
move=>hP hQ hBetween hEP hEQ hEB.
have hComposite:=pointed_holomorphic_pullback_composes hEQ hEB.
apply:(pointed_holomorphic_pullback_map_extensional hEP hComposite).
exact:(@holomorphic_adjacent_prefix_composition R X n omega j hJN hJ1N P Q between hP hQ hBetween).
Qed.
