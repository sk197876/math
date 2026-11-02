(** Federer (1969), 2.5.9, p. 100: continuous extension from a dense lattice
    in L1. The erratum p. 2, book p. 100 line 22, specifies density of L+ in
    total L1+. Neither reference states this abstract extension lemma. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [is_pseudometric_on_set]: supporting distance laws
    for the L1 extension in Federer 2.5.9, p. 100.
    Distinct total functions may have distance zero. *)
Definition is_pseudometric_on_set (R : realType) (T : Type)
    (W : set T) (d : T -> T -> R) :=
  (forall x y, W x -> W y -> 0 <= d x y) /\
  (forall x, W x -> d x x=0) /\
  (forall x y, W x -> W y -> d x y=d y x) /\
  (forall x y z, W x -> W y -> W z -> d x z <= d x y+d y z).

(** Source for [is_scalar_lipschitz_on_set]: supporting quantitative
    continuity for the norm-one extension in Federer 2.5.9,
    p. 100. The Lipschitz constant is one. *)
Definition is_scalar_lipschitz_on_set (R : realType) (T : Type)
    (D : set T) (d : T -> T -> R) (A : T -> R) :=
  forall x y, D x -> D y -> `|A x-A y| <= d x y.

(** Source for [is_scalar_lipschitz_extension]: abstract agreement
    and continuity specification supporting Federer 2.5.9, p. 100.
    Existence and density-based uniqueness are proved separately. *)
Definition is_scalar_lipschitz_extension (R : realType) (T : Type)
    (W D : set T) (d : T -> T -> R) (A B : T -> R) :=
  (forall x, D x -> B x=A x) /\ is_scalar_lipschitz_on_set W d B.

(** Source for [is_pseudometric_dense_subset]: epsilon form of the
    positive-lattice density in Federer 2.5.9, p. 100, erratum p. 2 line 22
    This abstracts the topology, not the density proof. *)
Definition is_pseudometric_dense_subset (R : realType) (T : Type)
    (W D : set T) (d : T -> T -> R) :=
  forall x, W x -> forall e : R, 0 < e -> exists y, D y /\ d x y < e.
