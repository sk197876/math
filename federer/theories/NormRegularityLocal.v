(** Federer (1969), 3.1.20, pp. 232–233: class-k maps obtained
    by gluing compatible local representatives and by locally
    stationary sequences. This is the public representation adapter
    for the class locality proved in 3.1.11, pp. 219–220. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import Hom RealNormUP ContinuousMultilinearUP ContinuousMultilinearSealed
  NormRegularity NormRegularityOperations NormClassHigherLocal.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Source for [norm_class_local]: local class-k representatives
    glue to class k on their union, supporting the limiting
    retraction of Federer 3.1.20, pp. 232–233. No convergence of
    derivatives is assumed: the representatives agree locally. *)
Lemma norm_class_local (R:realType) (X Y:lmodType R)
    (NX:X->R) (NY:Y->R) (hNX:is_real_norm NX) (hNY:is_real_norm NY)
    (A:X->Prop) (f:X->Y) k :
  (forall a, A a -> exists O:X->Prop, O a /\ (forall x, O x -> A x) /\
    norm_class hNX hNY O f k) -> norm_class hNX hNY A f k.
Proof.
exact (@norm_class_higher_local R X Y NX NY hNX hNY
  (fun j=>@ContinuousMultilinear.space R j X Y NX NY hNX hNY)
  (fun j=>@ContinuousMultilinear.evaluation R j X Y NX NY hNX hNY)
  (fun j=>@ContinuousMultilinear.norm R j X Y NX NY hNX hNY)
  (fun j=>@ContinuousMultilinear.laws R j X Y NX NY hNX hNY) A f k).
Qed.

(** Source for [norm_class_local_representatives]: the local
    stabilization argument at the end of the forward proof of
    Federer 3.1.20, p. 233. Locally equal class-k representatives
    give a class-k map on the actual domain. Supporting lemma. *)
Lemma norm_class_local_representatives (R:realType) (X Y:lmodType R)
    (NX:X->R) (NY:Y->R) (hNX:is_real_norm NX) (hNY:is_real_norm NY)
    (A:X->Prop) (f:X->Y) k :
  (forall a, A a -> exists (O:X->Prop) (g:X->Y),
    O a /\ (forall x, O x -> A x) /\ norm_class hNX hNY O g k /\
    forall x, O x -> g x=f x) -> norm_class hNX hNY A f k.
Proof.
move=>hlocal; apply: norm_class_local=>a ha.
have [O [g [hOa [hOA [hg heq]]]]]:=hlocal a ha.
exists O; split=>//; split=>//.
exact: norm_class_domain_agreement heq hg.
Qed.
