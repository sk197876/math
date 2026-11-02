(** Federer (1969), 3.2.37, p. 274: the finite family of
    disjoint compact subsets, each with its own orthogonal projection,
    in the Gross-measure supremum. Specify the family independently
    of any measure bound or choice of approximation. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets
  reals constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric
  EuclideanLebesgueDimensions CoordinateProjection.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [is_finite_compact_projected_family]: the finite
    compact-family data in the paragraph following the last display
    of Federer 3.2.37, p. 274. A finite index type presents the
    printed set family; repeated empty pieces have cost zero. *)
Record is_finite_compact_projected_family (R:realType) n m
    (A:set (inner_metric_space (@euclidean_inner_productP R n))) (I:finType)
    (K:I->set (inner_metric_space (@euclidean_inner_productP R n)))
    (p:I->{linear R_n R n->R_n R m}):Prop:={
  (** Source for [compact_projected_family_compact]: each member
      is compact, Federer 3.2.37, p. 274. *)
  compact_projected_family_compact:forall i,compact (K i);
  (** Source for [compact_projected_family_subset]: each member
      lies in the original A, Federer 3.2.37, p. 274. *)
  compact_projected_family_subset:forall i,K i `<=` A;
  (** Source for [compact_projected_family_projection]: each actual
      p_S belongs to O*(n,m), Federer 3.2.37, p. 274. *)
  compact_projected_family_projection:forall i,O_star (p i);
  (** Source for [compact_projected_family_disjoint]: distinct
      compact members are disjoint, Federer 3.2.37, p. 274. *)
  compact_projected_family_disjoint:forall i j,i!=j ->forall x,K i x ->K j x ->False
}.

(** Source for [compact_projected_family_values]: the actual
    finite sums whose supremum is Gross measure on Borel A,
    Federer 3.2.37, p. 274. The empty finite family is retained. *)
Definition compact_projected_family_values (R:realType) n m
    (A:set (inner_metric_space (@euclidean_inner_productP R n))):set (\bar R):=
  [set v|exists (I:finType)
    (K:I->set (inner_metric_space (@euclidean_inner_productP R n)))
    (p:I->{linear R_n R n->R_n R m}),
    is_finite_compact_projected_family A K p /\
      v=(\sum_i @euclidean_lebesgue_measure R m (p i @` K i))].
