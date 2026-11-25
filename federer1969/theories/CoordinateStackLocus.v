(** Federer (1969), 3.2.9, p. 247: every
    full-target-rank differential becomes injective after
    adjoining one of the finite coordinate projections
    of complementary dimension. *)
From mathcomp Require Import all_boot all_order all_algebra reals classical_sets.
From Federer Require Import Hom GrassmannAbbreviations ExteriorIndices CoordinateProjection EuclideanInnerProduct InnerNorm
  NormDifferentialUP InjectiveDifferentialPieceUP CoordinateInverseCoverUP EuclideanStackedMap EuclideanStackedKernel
  EpimorphismCoordinateSeparation.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [coordinate_projection_hom]: the fixed
    coordinate p_lambda in the proof of
    Federer 3.2.9, p. 247, expressed in
    the project's abstract linear-map carrier. *)
Definition coordinate_projection_hom (R:realType) m k (lambda:Lambda m k):
    Hom (R_n R m) (R_n R k):=
  hom_of_linear (GRing.Linear.clone _ _ _ _ (@coordinate_projection R m k lambda) _).

(** Source for [coordinate_stack_map]: U_lambda=(f,p_lambda)
    in Federer 3.2.9, p. 247, with
    Cartesian coordinates identified isometrically by blocks. *)
Definition coordinate_stack_map (R:realType) m n k
    (f:R_n R m->R_n R n) (lambda:Lambda m k):=
  euclidean_stacked_map f (@coordinate_projection_hom R m k lambda).

(** Source for [surjective_differential_coordinate_stack_cover]:
    the inclusion in the union of A_lambda
    in Federer 3.2.9, p. 247. The
    actual derivative of the chosen stacked map
    is injective, with no added hypothesis on f. *)
Theorem surjective_differential_coordinate_stack_cover (R:realType) n k
    (f:R_n R (n+k)->R_n R n) a:
  surjective_differential_locus f a -> exists lambda:Lambda (n+k) k,
    injective_differential_locus (coordinate_stack_map f lambda) a.
Proof.
move=>[L [hL hSurj]].
have [lambda hSep]:=epimorphism_coordinate_kernel_separation hSurj.
exists lambda.
pose p:=@coordinate_projection_hom R (n+k) k lambda.
exists (euclidean_stacked_linear_map L p); split.
- exact (euclidean_stacked_differential p hL).
- apply:euclidean_stacked_kernel_injective=>x hx hp.
  apply:(hSep x hx).
  exact hp.
Qed.
