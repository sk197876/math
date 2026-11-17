(** Federer (1969), 3.4.12, p. 339: local holomorphic sheets
    replace the inequality-defined real selections in 3.4.8(10),
    pp. 332–333. State the exact finite covering laws before
    proving existence. Every branch is local to one base neighbourhood;
    the definition imposes no global choice of sheets. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormMetric ScalarRestriction ComplexScalarSealed
  HolomorphicUP MetricSubsetBackground.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Section Cover.
Variable R:realType.
Variables X Y:lmodType (ComplexScalars.C R).
Variables (NX:X->R) (NY:Y->R).
Variable hNX:@is_real_norm R (restricted_space (ComplexScalars.embed R) X) NX.
Variable hNY:@is_real_norm R (restricted_space (ComplexScalars.embed R) Y) NY.
Local Notation XT:=(real_norm_metric_space hNX).
Local Notation YT:=(real_norm_metric_space hNY).
Variable Z:set XT.
Variable V:set YT.
Variable P:Hom X Y.
Variable k:nat.
(** Source for [is_finite_holomorphic_projection_cover]: the original
    projection has k disjoint local holomorphic inverse branches over
    every base point. Their relatively open images exhaust the original
    inverse image. This is the complex local covering assertion used
    in 3.4.12, p. 339; it assumes no existence theorem. *)
Record is_finite_holomorphic_projection_cover:Prop:={
  (** Source for [holomorphic_cover_projection_continuous]: continuity
      of the actual original projection, 3.4.12, p. 339. *)
  holomorphic_cover_projection_continuous:
    continuous (fun x:[the metricType R of metric_subset Z]=>(P (val x):YT));
  (** Source for [holomorphic_cover_projection_maps]: the original
      domain maps to the stated base, 3.4.12, p. 339. *)
  holomorphic_cover_projection_maps:forall x,Z x ->V (P x);
  (** Source for [holomorphic_cover_local_branches]: local complex
      sheets with every original inverse, disjointness and exhaustion
      equation, as required in 3.4.12, p. 339. *)
  holomorphic_cover_local_branches:forall y,V y ->exists (W:set YT) (s:'I_k->Y->X),
    @open YT W /\W y /\W `<=` V /\
    (forall i,@is_holomorphic R Y X NY NX hNY hNX W (s i)) /\
    (forall i z,W z ->Z (s i z) /\P (s i z)=z) /\
    (forall i j z,W z ->s i z=s j z ->i=j) /\
    (forall x,Z x /\W (P x) <->exists i:'I_k,W (P x) /\s i (P x)=x) /\
    forall i,exists O:set XT,@open XT O /\s i @` W=Z `&` O
}.
End Cover.
