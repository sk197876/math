(** Federer (1969), 4.1.2, p. 348: the
    finite Borel partition and its chosen points used
    to justify the integral/distribution interchange. Empty
    cells may remain with zero measure; all nonempty
    cells have an actual member as their tag. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals topology.
From Federer Require Import TopologicalBorel.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [is_finite_tagged_borel_partition]: the A_k
    and a_k in Federer 4.1.2, p. 348.
    The mesh bound controls the distance to the
    actual tag. No partition construction is prescribed. *)
Record is_finite_tagged_borel_partition (R:realType) (X:metricType R)
    (K:set X) (e:R) (I:finType) (A:I->set X) (tag:I->X):Prop:={
  (** Source for [finite_tagged_partition_borel]: Borel cells,
      Federer 4.1.2, p. 348. *)
  finite_tagged_partition_borel:forall i,borel_set (A i);
  (** Source for [finite_tagged_partition_inside]: the cells
      lie in the original compact, Federer 4.1.2, p. 348. *)
  finite_tagged_partition_inside:forall i,A i `<=` K;
  (** Source for [finite_tagged_partition_cover]: the cells
      cover the original compact, Federer 4.1.2, p. 348. *)
  finite_tagged_partition_cover:forall x,K x ->exists i,A i x;
  (** Source for [finite_tagged_partition_disjoint]: the original
      cells are disjoint, Federer 4.1.2, p. 348. *)
  finite_tagged_partition_disjoint:forall i j x,A i x ->A j x ->i=j;
  (** Source for [finite_tagged_partition_tag]: every nonempty
      cell has its tag inside it, Federer 4.1.2, p. 348. *)
  finite_tagged_partition_tag:forall i,A i !=set0 ->A i (tag i);
  (** Source for [finite_tagged_partition_mesh]: small diameters
      give the required tag-distance bound in Federer
      4.1.2, p. 348. *)
  finite_tagged_partition_mesh:forall i x,A i x ->mdist x (tag i)<=e
}.
