(** Federer (1969), 3.2.9, p. 247: choose
    a coordinate projection p_lambda whose kernel
    meets ker L only at zero for each
    surjective actual differential L. Use the
    proved kernel frame and 1.7.4 coordinate separation. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import Hom GrassmannAbbreviations FiniteCoordinates ExteriorIndices CoordinateProjection
  EuclideanKernelFrameUP EuclideanKernelFrameExistence CoordinateFamilySeparation.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [epimorphism_coordinate_kernel_separation]:
    the coordinate choice behind the union of
    A_lambda in Federer 3.2.9, p. 247.
    Surjectivity gives a frame of the exact
    complementary size; the selected coordinate projection
    separates every vector in the actual kernel. *)
Theorem epimorphism_coordinate_kernel_separation (R:realType) n k
    (L:Hom (R_n R (n+k)) (R_n R n)):
  (forall y,exists x,L x=y) -> exists lambda:Lambda (n+k) k,
    forall x,L x=0 -> coordinate_projection lambda x=0 -> x=0.
Proof.
move=>hSurj.
have [e [hIndependent hKernel]]:=euclidean_epimorphism_kernel_frame_exists hSurj.
have [lambda hSep]:=coordinate_projection_separates_finite_span hIndependent.
exists lambda=>x hx hp; exact (hSep x ((hKernel x).1 hx) hp).
Qed.
