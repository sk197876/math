(** Federer (1969), 2.10.3, p. 172: the map sending its 2m endpoints to the
    exterior product of their m differences is affine in each endpoint.
    Formalise the printed assertion using a paired index domain and the
    public factor-linearity laws. This argument works in any real vector
    space; the target measure itself is Euclidean as printed. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import ExteriorGrading FiniteExteriorPowers AffineMaps
  SeparateAffineHullBound ExteriorCoordinateLinearity.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [paired_exterior_product]: direct 2m-variable
    endpoint map described by Federer 2.10.3, p. 172.
    False selects the first endpoint of a difference and
    true selects the second. *)
Definition paired_exterior_product (K : fieldType) (V : lmodType K)
    (m : nat) (p : ('I_m*bool)%type -> V) : exterior_power V m :=
  e_lambda (fun i => p (i,false)-p (i,true)) (ord_tuple m).

(** Source for [paired_exterior_product_replacement]:
    supporting single-endpoint substitution for the affine
    claim in Federer 2.10.3, p. 172. Changing one
    endpoint changes just one vector factor by an affine
    translation or translated negation. *)
Lemma paired_exterior_product_replacement (K : fieldType) (V : lmodType K)
    (m : nat) (p : ('I_m*bool)%type -> V) (i : 'I_m) (e : bool) (x : V) :
  paired_exterior_product (coordinate_replacement p (i,e) x)=
    exterior_coordinate_map (fun j => p (j,false)-p (j,true)) i
      (if e then p (i,false)-x else x-p (i,true)).
Proof.
rewrite /paired_exterior_product /exterior_coordinate_map.
have he : (fun j => coordinate_replacement p (i,e) x (j,false)-
    coordinate_replacement p (i,e) x (j,true))=
    coordinate_replacement (fun j => p (j,false)-p (j,true)) i
      (if e then p (i,false)-x else x-p (i,true)).
  apply: funext=> j; rewrite /coordinate_replacement !xpair_eqE /=.
  by case: e; case: eqP=> [->|hji].
by rewrite he.
Qed.

(** Source for [paired_exterior_product_separately_affine]:
    direct separate-affinity assertion of Federer 2.10.3,
    p. 172. Use the proved linearity in a vector
    factor and the affine dependence of its difference
    on either endpoint. No finite dimension is required. *)
Theorem paired_exterior_product_separately_affine (R : realType) (V : lmodType R)
    (m : nat) (p : ('I_m*bool)%type -> V) (k : ('I_m*bool)%type) :
  is_affine_map (fun x => paired_exterior_product (coordinate_replacement p k x)).
Proof.
case: k=> i e; move=> x y a b hab; rewrite !paired_exterior_product_replacement.
case: e=> /=.
- have he : p (i,false)-(a *: x+b *: y)=
      a *: (p (i,false)-x)+b *: (p (i,false)-y).
    by rewrite !scalerBr addrACA -scalerDl hab scale1r -opprD.
  by rewrite he linearD !linearZ.
- have he : (a *: x+b *: y)-p (i,true)=
      a *: (x-p (i,true))+b *: (y-p (i,true)).
    by rewrite !scalerBr addrACA -opprD -scalerDl hab scale1r.
  by rewrite he linearD !linearZ.
Qed.
