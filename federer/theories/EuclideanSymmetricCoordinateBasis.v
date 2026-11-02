(** Federer (1969), 3.2.28(1), printed p. 263:
    a basis of the actual symmetric endomorphism space,
    indexed by i<=j. The coordinate construction is
    confined to this opaque existence proof. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import Hom TensorUP ModuleQuotient SubspaceCarrier
  LinearBasis FiniteIndependence FiniteBasisCriterion GrassmannAbbreviations
  EuclideanSymmetricEndomorphismSpace EuclideanSymmetricCoordinates EuclideanSymmetricGenerators
  EuclideanSymmetricUpperCoordinates EuclideanSymmetricCoordinateFunctionals.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [euclidean_symmetric_upper_basis_exists]:
    the m(m+1)/2 independent entries give a basis
    of Y_m, supporting the dimension calculation in
    Federer 3.2.28(1), p. 263. This theorem proves
    the basis before the separate index-cardinality calculation. *)
Theorem euclidean_symmetric_upper_basis_exists (R:realType) m:
  exists e:euclidean_symmetric_indices m->
    subspace_space (@euclidean_symmetric_hom_subspace R m),
    is_basis e /\ forall a b,
      euclidean_symmetric_upper_coordinate a (e b)=if b==a then 1 else 0.
Proof.
pose I:=euclidean_symmetric_indices m.
pose Y:=subspace_space (@euclidean_symmetric_hom_subspace R m).
pose e (a:I):Y:=subspace_lift
  (@euclidean_symmetric_generator_membership R m (val a).1 (val a).2).
have hEntry a b:euclidean_symmetric_upper_coordinate a (e b)=
    if b==a then 1 else 0.
  change (euclidean_hom_coefficient
    (@euclidean_symmetric_generator R m (val b).1 (val b).2)
    (val a).1 (val a).2=if b==a then 1 else 0).
  exact:euclidean_symmetric_upper_coefficient.
have hIndependent:finite_independent e.
  apply:(@finite_independent_separating R I Y e
    (fun a=>hom_as_linear (@euclidean_symmetric_upper_coordinate R m a)))=>a b.
  change (euclidean_symmetric_upper_coordinate a (e b)=if a==b then 1 else 0).
  by rewrite hEntry eq_sym.
exists e; split=>//.
apply:(@finite_basis_criterion R I Y e hIndependent)=>y.
exists (fun a=>euclidean_symmetric_upper_coordinate a y).
apply:euclidean_symmetric_upper_coordinates_injective=>b.
rewrite linear_sum.
change (euclidean_symmetric_upper_coordinate b y=
  \sum_a euclidean_symmetric_upper_coordinate b
    (euclidean_symmetric_upper_coordinate a y*:e a)).
have hTerm a:euclidean_symmetric_upper_coordinate b
    (euclidean_symmetric_upper_coordinate a y*:e a)=
    euclidean_symmetric_upper_coordinate a y*(if a==b then 1 else 0).
  rewrite linearZ.
  change (euclidean_symmetric_upper_coordinate a y*
    euclidean_symmetric_upper_coordinate b (e a)=
    euclidean_symmetric_upper_coordinate a y*(if a==b then 1 else 0)).
  by rewrite hEntry.
under eq_bigr do rewrite hTerm.
change (euclidean_symmetric_upper_coordinate b y=
  \sum_a euclidean_symmetric_upper_coordinate a y*(if a==b then 1 else 0)).
rewrite (bigD1 b) //= eqxx mulr1.
have hz:(\sum_(a | a!=b)
    euclidean_symmetric_upper_coordinate a y*(if a==b then 1 else 0))=0.
  apply:big1=>a ha; by rewrite (negbTE ha) mulr0.
by rewrite hz addr0.
Qed.
