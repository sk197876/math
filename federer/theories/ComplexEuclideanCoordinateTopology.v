(** Federer (1969), 3.4.12, p. 339: the original complex
    coordinate space has the topology of the real space with twice
    as many coordinates. Use the checked exact norm equalities
    and bounded linear continuity; both inverse maps are retained. *)
From mathcomp Require Import all_boot all_order all_algebra reals topology.
From Federer Require Import Hom RealNormUP NormMetric ScalarRestriction ComplexScalarSealed ComplexNormUP
  FiniteCoordinates GrassmannAbbreviations EuclideanInnerProduct InnerNorm HilbertFormCompactness
  HolomorphicCoordinateNorm ComplexEuclideanCoordinates NormDifferentialUP NormBoundedLinearTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Section Coordinates.
Variable R:realType.
Variable n:nat.
Local Notation X:=(coordinate_space (ComplexScalars.C R) n).
Local Notation XR:=(restricted_space (ComplexScalars.embed R) X).
Local Notation Y:=(R_n R (n+n)).
Local Notation NX:=(@holomorphic_coordinate_norm R n).
Local Notation NY:=(inner_norm (@euclidean_inner_productP R (n+n))).
Local Notation hNX:=(complex_norm_real (@holomorphic_coordinate_norm_laws R n)).
Local Notation hNY:=(inner_norm_real_norm (@euclidean_inner_productP R (n+n))).
(** Source for [complex_real_coordinate_hom_bounded]: the original
    complex-to-real coordinate identification preserves the norm,
    supporting 3.4.12, p. 339. *)
Lemma complex_real_coordinate_hom_bounded:
  @norm_bounded_linear R XR Y NX NY (@complex_real_coordinate_hom R n).
Proof.
exists 1;split;first exact:ler01.
move=>x;change (is_true (NY ((@complex_real_coordinate_hom R n x))<=1*NX x)).
by rewrite -complex_euclidean_coordinate_norm mul1r.
Qed.
(** Source for [complex_from_real_coordinate_hom_bounded]: the
    inverse original real-coordinate identification also preserves
    the norm, supporting 3.4.12, p. 339. *)
Lemma complex_from_real_coordinate_hom_bounded:
  @norm_bounded_linear R Y XR NY NX (@complex_from_real_coordinate_hom R n).
Proof.
exists 1;split;first exact:ler01.
move=>y;change (is_true (NX ((@complex_from_real_coordinate_hom R n y))<=1*NY y)).
by rewrite complex_inverse_euclidean_coordinate_norm mul1r.
Qed.
(** Source for [complex_real_coordinate_hom_continuous]: continuity
    of the actual complex-to-real coordinates, used to transfer
    the real component theorem in 3.4.12, p. 339. *)
Lemma complex_real_coordinate_hom_continuous:
  continuous (fun x:real_norm_metric_space hNX=>((@complex_real_coordinate_hom R n x):real_norm_metric_space hNY)).
Proof. exact:(@norm_bounded_linear_continuous R XR Y NX NY hNX hNY _ complex_real_coordinate_hom_bounded). Qed.
(** Source for [complex_from_real_coordinate_hom_continuous]:
    continuity of the original inverse coordinates, used in the
    real-case component argument of 3.4.12, p. 339. *)
Lemma complex_from_real_coordinate_hom_continuous:
  continuous (fun y:real_norm_metric_space hNY=>((@complex_from_real_coordinate_hom R n y):real_norm_metric_space hNX)).
Proof. exact:(@norm_bounded_linear_continuous R Y XR NY NX hNY hNX _ complex_from_real_coordinate_hom_bounded). Qed.
End Coordinates.
