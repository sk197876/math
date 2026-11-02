(** Supporting finite-coordinate argument for Federer (1969), 2.10.3, p.
    172: affineness in each of the 2m variables permits replacing each
    variable's source by its convex hull without increasing the norm
    supremum. Prove the abstract finite-coordinate statement before applying
    it to exterior products. No finite-dimensionality of the vector spaces
    is needed by this supporting theorem. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import AffineMaps ConvexHull RealNormUP AffineConvexPreimage.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [coordinate_replacement]: supporting single-
    variable substitution in the separately affine map of
    Federer 2.10.3, p. 172. The family domain records
    the variables rather than encoding their number alone. *)
Definition coordinate_replacement (I : eqType) (V : Type)
    (u : I -> V) (i : I) (x : V) : I -> V :=
  fun j => if j==i then x else u j.

(** Source for [coordinate_replacement_self]: supporting
    identity substitution for the finite-variable hull
    argument of Federer 2.10.3, p. 172. *)
Lemma coordinate_replacement_self (I : eqType) (V : Type) (u : I -> V) i :
  coordinate_replacement u i (u i)=u.
Proof. apply: funext=> j; rewrite /coordinate_replacement; by case: eqP=> [->|]. Qed.

(** Source for [separately_affine_norm_bound_convex_hull]:
    supporting finite iteration of the affine-variable
    argument in Federer 2.10.3, p. 172. Each norm
    sublevel section is convex; extend the bound through
    the finite coordinate list using the hull's universal
    property. Empty index sets are also permitted in this
    abstract support lemma. *)
Theorem separately_affine_norm_bound_convex_hull (R : realType)
    (I : finType) (V W : lmodType R) (F : (I -> V) -> W)
    (N : W -> R) (hN : is_real_norm N) (A : set V) (b : R) :
  (forall u i, is_affine_map (fun x => F (coordinate_replacement u i x))) ->
  (forall u, (forall i, A (u i)) -> N (F u)<=b) ->
  forall u, (forall i, convex_hull A (u i)) -> N (F u)<=b.
Proof.
move=> hF hA u hu.
have hstep : forall s : seq I, uniq s -> forall v : I -> V,
    (forall i, i \in s -> convex_hull A (v i)) ->
    (forall i, i \notin s -> A (v i)) -> N (F v)<=b.
  elim=> [|i s ih] hs v hvhout hvAout.
  - apply: hA=> j; exact: hvAout j (erefl true).
  - have /andP[his hs'] := hs.
    have hb x : A x -> N (F (coordinate_replacement v i x))<=b.
      move=> hx; apply: (ih hs').
      + move=> j hj.
        have hji : j!=i by apply/eqP=> he; move: his; rewrite -he hj.
        rewrite /coordinate_replacement (negPf hji).
        apply: hvhout; by rewrite inE hj orbT.
      + move=> j hj; case: (eqVneq j i)=> [hji|hji].
        * by rewrite /coordinate_replacement hji eqxx.
        * rewrite /coordinate_replacement (negPf hji).
          apply: hvAout; by rewrite inE negb_or hji hj.
    have hx : convex_hull A (v i) by apply: hvhout; rewrite inE eqxx.
    have hh := @affine_norm_bound_convex_hull R V W
      (fun x => F (coordinate_replacement v i x)) N hN A b (hF v i) hb (v i) hx.
    by rewrite coordinate_replacement_self in hh.
apply: (hstep (enum I) (enum_uniq I)).
- by move=> i _; exact: hu.
- by move=> i; rewrite mem_enum.
Qed.
