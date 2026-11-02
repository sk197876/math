(** Federer (1969), 3.2.33, p. 270: analyticity
    relative to an analytic submanifold. This is the analytic
    version of the local ambient-extension convention in
    3.1.22, p. 236; coordinate equivalence is proved separately. *)
From mathcomp Require Import all_boot all_order all_algebra reals classical_sets.
From Federer Require Import RealNormUP NormAnalyticUP NormAnalyticLocal RelativeClassUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [norm_analytic_relative]: f is analytic on
    W in the final paragraph of Federer 3.2.33, p. 270.
    Each point has an actual ambient analytic representative
    agreeing with f on W near that point. A records the
    original domain. This independent local predicate selects
    no extension; analytic coordinates prove its intrinsic
    interpretation, as for the relative class definition. *)
Definition norm_analytic_relative (R:realType) (X Y:lmodType R)
    (NX:X->R) (NY:Y->R) (hNX:is_real_norm NX) (hNY:is_real_norm NY)
    (A W:set X) (f:X->Y):=
  forall a,W a ->exists (U:set X) (g:X->Y),
    U a /\@norm_analytic R X Y NX NY hNX hNY U g /\
    forall x,W x ->U x ->A x /\f x=g x.

(** Source for [norm_analytic_relative_class]: analytic f on
    W is relatively of every differentiability class, supporting
    actual relative differentials in Federer 3.2.33, p. 270,
    by 3.1.24, p. 239. The same local analytic
    representative supplies each class; no outside-domain
    value or global extension is required. *)
Lemma norm_analytic_relative_class (R:realType) (X Y:lmodType R)
    (NX:X->R) (NY:Y->R) (hNX:is_real_norm NX) (hNY:is_real_norm NY)
    (A W:set X) (f:X->Y):
  @norm_analytic_relative R X Y NX NY hNX hNY A W f ->forall k,
  @norm_class_relative R X Y NX NY hNX hNY A W f k.
Proof.
move=>hf k a ha; have [U [g [haU [hg hAgree]]]]:=hf a ha.
exists U,g; split; first exact haU.
split; last exact hAgree.
exact:(norm_analytic_class_all_orders hg k).
Qed.
