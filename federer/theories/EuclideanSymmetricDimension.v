(** Federer (1969), 3.2.28(1), printed p. 263:
    dim Y_m=m(m+1)/2 for the actual symmetric
    endomorphism space, including m=0. Dimension is
    specified by the existence and uniqueness of a basis size. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import ModuleQuotient SubspaceCarrier LinearBasis
  FiniteBasisComparison HomCompositionDeterminant
  EuclideanSymmetricEndomorphismSpace EuclideanSymmetricUpperCoordinates
  EuclideanSymmetricCoordinateBasis EuclideanSymmetricIndexCardinality.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope nat_scope.

(** Source for [euclidean_symmetric_dimension_basis]: the
    actual Y_m has a basis with m(m+1)/2 elements,
    Federer 3.2.28(1), p. 263. The coordinate witnesses
    remain confined to proved existence; no global basis is chosen. *)
Theorem euclidean_symmetric_dimension_basis (R:realType) m:
  exists e:'I_(m*(m+1)%/2)->
    subspace_space (@euclidean_symmetric_hom_subspace R m), is_basis e.
Proof.
have [e [he hEntry]]:=@euclidean_symmetric_upper_basis_exists R m.
rewrite -(euclidean_symmetric_index_cardinality m).
exists (fun i=>e (enum_val i)).
exact:(@basis_reindex R (Choice.clone (euclidean_symmetric_indices m) _)
  (Choice.clone 'I_#|{:euclidean_symmetric_indices m}| _)
  (subspace_space (@euclidean_symmetric_hom_subspace R m)) e he
  enum_rank enum_val (@enum_rankK (euclidean_symmetric_indices m))
  (@enum_valK (euclidean_symmetric_indices m))).
Qed.

(** Source for [euclidean_symmetric_dimension_unique]: every
    finite basis of Y_m has size m(m+1)/2,
    Federer 3.2.28(1), p. 263, by the dimension
    invariance of 1.6.1, p. 23. *)
Theorem euclidean_symmetric_dimension_unique (R:realType) m q
    (b:'I_q->subspace_space (@euclidean_symmetric_hom_subspace R m)):
  is_basis b ->q=m*(m+1)%/2.
Proof.
move=>hb; have [e he]:=@euclidean_symmetric_dimension_basis R m.
exact:finite_basis_size hb he.
Qed.
