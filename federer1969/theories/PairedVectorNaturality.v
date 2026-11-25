(** Federer (1969), 1.8.2, p. 40: the paired normal-form
    volume on the associated space maps to the corresponding paired
    volume in the ambient space. When each second member is i times
    the first, this is precisely the printed complex paired product. *)
From mathcomp Require Import all_boot all_order all_algebra.
From mathcomp.classical Require Import boolp.
From Federer Require Import SimpleVectors CovectorProductNaturality
  ConcatenatedFamilies PairedRealVectors ScalarRestriction ComplexScalarSealed
  ComplexPairedVectors ComplexOrderedBases.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [paired_real_vector_natural]: Federer 1.8.2,
    p. 40, the inclusion sends the paired volume to the product
    of the image pairs. More generally this holds for any linear map. *)
Theorem paired_real_vector_natural (K : fieldType) (V W : lmodType K)
    (f : {linear V -> W}) k (a b : 'I_k -> V) :
  exterior_power_map f (k+k) (paired_real_vector a b) =
    paired_real_vector (fun i => f (a i)) (fun i => f (b i)).
Proof.
rewrite /paired_real_vector linearZ exterior_basis_product_natural.
have hc : (fun i => f (concatenate_family a b i)) =
    concatenate_family (fun i => f (a i)) (fun i => f (b i)).
  apply: funext => i; by rewrite /concatenate_family; case: (split i).
by rewrite hc.
Qed.

(** Source for [paired_real_complex_identification]: Federer 1.8.2,
    p. 40, a_1 wedge (i a_1) wedge ... wedge a_k wedge (i a_k)
    is the complex paired vector already used in 1.6.6, p. 27. *)
Lemma paired_real_complex_identification (R : realFieldType)
    (V : lmodType (ComplexScalars.C R)) k (a : 'I_k -> V) :
  @paired_real_vector R (restricted_space (ComplexScalars.embed R) V) k a
    (fun i => ComplexScalars.ii R *: a i) = paired_complex_vector a.
Proof. by []. Qed.
