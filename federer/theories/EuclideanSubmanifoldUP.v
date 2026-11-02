(** Federer (1969), 3.1.19, p. 231: a mu-dimensional submanifold of
    class k is specified by local diffeomorphisms straightening it to
    mu-dimensional vector subspaces. This definition applies also to
    class zero, dimension zero and the empty subset. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import Hom ModuleQuotient SubspaceCarrier GrassmannSubspaces
  GrassmannAbbreviations EuclideanInnerProduct InnerNorm HilbertFormCompactness
  NormDifferentialUP NormRegularity NormDiffeomorphismUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [relatively_open_set]: a relatively open subset of B,
    used in condition (3) of Federer 3.1.19, p. 231. This is general
    topology: the intersection of B with an ambient open subset. *)
Definition relatively_open_set (T:topologicalType) (B W:set T) :=
  exists O:set T, open O /\ W=B `&` O.

Section Submanifold.
Variable R:realType.
Variable n:nat.
Local Notation X:=(R_n R n).
Local Notation NX:=(inner_norm (@euclidean_inner_productP R n)).
Local Notation hNX:=(inner_norm_real_norm (@euclidean_inner_productP R n)).

(** Source for [is_submanifold_straightening]: condition (1) in
    Federer 3.1.19, p. 231: sigma(B intersect T)=Z intersect image sigma,
    with T a neighbourhood of b and sigma a class-k diffeomorphism.
    The target image C is explicit, and Z has its actual dimension. *)
Record is_submanifold_straightening mu k (B:set X) b (T C:set X)
    (sigma tau:X->X) (Z:G X mu) : Prop := {
  (** Source for [submanifold_straightening_neighbourhood]: T is a
      neighbourhood of b in condition (1), Federer 3.1.19, p. 231. *)
  submanifold_straightening_neighbourhood : norm_domain_interior NX T b;
  (** Source for [submanifold_straightening_diffeomorphism]: the actual
      class-k diffeomorphism sigma and its inverse in condition (1),
      Federer 3.1.19, p. 231. *)
  submanifold_straightening_diffeomorphism : is_norm_diffeomorphism hNX hNX T C sigma tau k;
  (** Source for [submanifold_straightening_image]: the exact plane
      section sigma(B intersect T), condition (1) of 3.1.19, p. 231. *)
  submanifold_straightening_image : sigma @` (B `&` T)=
    [set z|grassmann_val Z z /\ C z]
}.

(** Source for [is_euclidean_submanifold]: the definition by condition
    (1) in Federer 3.1.19, p. 231. The existence of the local maps and
    subspace must be proved at every point; no object or axiom is
    postulated by this predicate. No nonemptiness is required. *)
Definition is_euclidean_submanifold mu k (B:set X) :=
  forall b, B b -> exists (T C:set X) (sigma tau:X->X) (Z:G X mu),
    is_submanifold_straightening k B b T C sigma tau Z.
End Submanifold.
