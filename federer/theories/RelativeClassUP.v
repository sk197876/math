(** Federer (1969), 3.1.22, p. 236: class k relative
    to a subset is specified by local ambient class-k extensions. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals.
From Federer Require Import RealNormUP NormRegularity.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [norm_class_relative]: the definition of class
    k relative to S in Federer 3.1.22, p. 236.
    At each a in S a class-k ambient representative agrees
    with f on S near a. A is the actual f-domain. *)
Definition norm_class_relative (R:realType) (X Y:lmodType R)
    (NX:X->R) (NY:Y->R) (hNX:is_real_norm NX) (hNY:is_real_norm NY)
    (A S:set X) (f:X->Y) k :=
  forall a,S a -> exists (U:set X) (g:X->Y),
    U a /\ norm_class hNX hNY U g k /\
    forall x,S x -> U x -> A x /\ f x=g x.

(** Source for [is_norm_relative_extension]: the single open
    ambient extension of a relatively class-k map in Federer
    3.1.22, p. 236. Its class laws imply openness
    of U; U contains all of S and agrees with the
    original function at every point of S. *)
Definition is_norm_relative_extension (R:realType) (X Y:lmodType R)
    (NX:X->R) (NY:Y->R) (hNX:is_real_norm NX) (hNY:is_real_norm NY)
    (A S:set X) (f:X->Y) k (U:set X) (g:X->Y) :=
  norm_class hNX hNY U g k /\ S `<=` U /\ forall x,S x -> A x /\ f x=g x.

(** Source for [norm_relative_extension_class]: the immediate
    reverse direction of the ambient-extension characterization
    in Federer 3.1.22, p. 236. A single extension
    supplies the local representatives in the defining predicate. *)
Lemma norm_relative_extension_class (R:realType) (X Y:lmodType R)
    (NX:X->R) (NY:Y->R) (hNX:is_real_norm NX) (hNY:is_real_norm NY)
    (A S:set X) (f:X->Y) k (U:set X) (g:X->Y) :
  @is_norm_relative_extension R X Y NX NY hNX hNY A S f k U g ->
  @norm_class_relative R X Y NX NY hNX hNY A S f k.
Proof.
move=>[hg [hSU hag]] a ha.
exists U,g; split; first exact: hSU a ha.
split=>// x hx _; exact: hag x hx.
Qed.

(** Source for [norm_class_relative_domain]: a function of
    class k relative to S is defined at every point of
    S, implicit in the agreement of restrictions in Federer
    3.1.22, p. 236. No outside-domain value is used. *)
Lemma norm_class_relative_domain (R:realType) (X Y:lmodType R)
    (NX:X->R) (NY:Y->R) (hNX:is_real_norm NX) (hNY:is_real_norm NY)
    (A S:set X) (f:X->Y) k :
  @norm_class_relative R X Y NX NY hNX hNY A S f k -> S `<=` A.
Proof.
move=>hf a ha; have [U [g [haU [hg hag]]]]:=hf a ha.
exact (hag a ha haU).1.
Qed.
