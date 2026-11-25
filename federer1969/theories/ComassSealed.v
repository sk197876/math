(** Federer (1969), 1.8.1, p. 38: the finite-dimensional comass, exposed by
    its supremum laws. The real-supremum witness is hidden by opaque module
    ascription. Source context and positive-degree convention:
    SimpleUnitBall.v. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp.
From Federer Require Import InnerProductUP AlternatingCoordinates LinearBasis
  ComassUP ComassConstruction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Module Type ComassSig.
(** Source for [norm]: Federer 1.8.1, p. 38, the comass
    of a positive-degree covector on a finite-dimensional inner-product space. *)
Parameter norm : forall (R : realType) (h2 : (1+1 : R) != 0)
    (V : lmodType R) (B : V -> V -> R) (hB : is_inner_product B)
    n (e : 'I_n -> V), is_basis e -> forall m, (0 < m)%N -> A_m V R^o m -> R.
(** Source for [laws]: Federer 1.8.1, p. 38, the comass
    satisfies the specified upper-bound and approximation properties. *)
Parameter laws : forall (R : realType) (h2 : (1+1 : R) != 0)
    (V : lmodType R) (B : V -> V -> R) (hB : is_inner_product B)
    n (e : 'I_n -> V) (he : is_basis e) m (hm : (0 < m)%N) (phi : A_m V R^o m),
    is_comass h2 hB phi (@norm R h2 V B hB n e he m hm phi).
End ComassSig.
Module Comass : ComassSig.
(** Source for [norm]: Federer 1.8.1, p. 38, select the
    proved supremum witness inside the opaque module. *)
Definition norm (R : realType) (h2 : (1+1 : R) != 0)
    (V : lmodType R) (B : V -> V -> R) (hB : is_inner_product B)
    n (e : 'I_n -> V) (he : is_basis e) m (hm : (0 < m)%N) (phi : A_m V R^o m) : R :=
  sval (constructive_indefinite_description (comass_exists h2 hB he hm phi)).
(** Source for [laws]: Federer 1.8.1, p. 38, the selected
    witness satisfies the public supremum specification. *)
Lemma laws (R : realType) (h2 : (1+1 : R) != 0)
    (V : lmodType R) (B : V -> V -> R) (hB : is_inner_product B)
    n (e : 'I_n -> V) (he : is_basis e) m (hm : (0 < m)%N) (phi : A_m V R^o m) :
    is_comass h2 hB phi (@norm R h2 V B hB n e he m hm phi).
Proof. exact: (svalP (constructive_indefinite_description (comass_exists h2 hB he hm phi))). Qed.
End Comass.
