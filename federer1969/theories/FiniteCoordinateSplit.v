(** Federer (1969), 2.6.6, p. 120: mu_a is "the cartesian product of the
    Daniell integrals mu_j corresponding to j in a (constructed by the
    method of 2.6.4)". The method of 2.6.4, p. 119, applies to a cartesian
    product of two spaces. This file supplies the identification of X_{a cup
    {i}} with X_a x X_i for i not in a, by which the finite products are
    built one factor at a time. The map psi(u) = (u|a, u(i)) is continuous
    and bijective, with continuous inverse; the inverse is written through a
    point x0 of the full product X and does not depend on x0. *)
From mathcomp Require Import all_boot choice all_order all_algebra finmap boolp mathcomp_extra classical_sets reals topology.
From Federer Require Import FiniteCoordinateProjection ProductCoordinateReplacement TopologicalProductMaps
  DependentProductContinuity.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Local Open Scope fset_scope.

Section Split.
Variables (I : choiceType) (Y : I -> topologicalType).
Local Notation X := (prod_topology Y).

(** Source for [finite_coordinate_coordinate_irrelevance]: supporting
    proof irrelevance for the coordinates of a point of X_a, Federer
    2.6.6, p. 120. *)
Lemma finite_coordinate_coordinate_irrelevance (F : {fset I}) (u : finite_coordinate_space Y F)
    (k : I) (h1 h2 : k \in F) :
  u (exist _ k h1)=u (exist _ k h2).
Proof. by rewrite (bool_irrelevance h1 h2). Qed.

(** Source for [finite_coordinate_split]: the identification of
    X_{a cup {i}} with X_a x X_i used to form the finite products of
    Federer 2.6.6, p. 120, by the binary method of 2.6.4, p. 119;
    psi(u) = (u|a, u(i)). *)
Definition finite_coordinate_split (F : {fset I}) (i : I)
    (u : finite_coordinate_space Y (i |` F)) : (finite_coordinate_space Y F * Y i)%type :=
  ((fun j : {j : I | j \in F}=>u (exist _ (val j) (fset1Ur i (valP j)))), u (exist _ i (fset1U1 i F))).

(** Source for [finite_coordinate_join]: the inverse of psi,
    supporting the identification of X_{a cup {i}} with X_a x X_i in
    Federer 2.6.6, p. 120. The point x0 of X only fills the
    coordinates outside a cup {i}, which p_{a cup {i}} discards. *)
Definition finite_coordinate_join (x0 : X) (F : {fset I}) (i : I)
    (q : (finite_coordinate_space Y F * Y i)%type) : finite_coordinate_space Y (i |` F) :=
  finite_coordinate_projection (F:=i |` F) (dfwith (finite_coordinate_section x0 q.1) i q.2).

(** Source for [finite_coordinate_split_projection]: psi o p_{a cup {i}}
    = (p_a, pi_i), supporting Federer 2.6.6, p. 120. *)
Lemma finite_coordinate_split_projection (F : {fset I}) (i : I) (x : X) :
  finite_coordinate_split (finite_coordinate_projection (F:=i |` F) x)=
    (finite_coordinate_projection (F:=F) x, x i).
Proof. by []. Qed.

(** Source for [finite_coordinate_split_continuous]: continuity of
    psi, supporting Federer 2.6.6, p. 120. *)
Lemma finite_coordinate_split_continuous (F : {fset I}) (i : I) :
  continuous (@finite_coordinate_split F i).
Proof.
apply: topological_pair_continuous.
- apply: dependent_product_map_continuous=> j.
  exact (@proj_continuous [the choiceType of {k : I | k \in i |` F}] (fun k=>Y (val k))
    (exist _ (val j) (fset1Ur i (valP j)))).
- exact (@proj_continuous [the choiceType of {k : I | k \in i |` F}] (fun k=>Y (val k))
    (exist _ i (fset1U1 i F))).
Qed.

(** Source for [finite_coordinate_join_continuous]: continuity of the
    inverse of psi, supporting Federer 2.6.6, p. 120. *)
Lemma finite_coordinate_join_continuous (x0 : X) (F : {fset I}) (i : I) :
  continuous (@finite_coordinate_join x0 F i).
Proof.
have hq : continuous (fun q : (finite_coordinate_space Y F * Y i)%type=>
    (q.2, finite_coordinate_section x0 q.1)).
  apply: topological_pair_continuous; first exact: second_projection_continuous.
  move=> q; exact: (continuous_comp (@first_projection_continuous _ _ q)
    (@finite_coordinate_section_continuous I Y x0 F q.1)).
have he : @finite_coordinate_join x0 F i=finite_coordinate_projection (F:=i |` F) \o
    (product_coordinate_replace (i:=i) \o (fun q : (finite_coordinate_space Y F * Y i)%type=>
    (q.2, finite_coordinate_section x0 q.1))) by [].
rewrite he=> q; apply: continuous_comp; last exact: finite_coordinate_projection_continuous.
apply: continuous_comp; first exact: hq.
exact: product_coordinate_replace_continuous.
Qed.

(** Source for [finite_coordinate_join_split]: the inverse of psi is a
    left inverse, supporting Federer 2.6.6, p. 120. *)
Lemma finite_coordinate_join_split (x0 : X) (F : {fset I}) (i : I)
    (u : finite_coordinate_space Y (i |` F)) :
  finite_coordinate_join x0 (finite_coordinate_split u)=u.
Proof.
apply: functional_extensionality_dep=> -[k hk].
rewrite /finite_coordinate_join /finite_coordinate_projection /=.
case: (eqVneq i k)=> [hik|hik].
- move: hk; rewrite -hik=> hk; rewrite dfwithin /=.
  exact: finite_coordinate_coordinate_irrelevance.
- rewrite dfwithout // /finite_coordinate_section.
  case: pselect=> h /=.
  + exact: finite_coordinate_coordinate_irrelevance.
  + exfalso; apply: h; move: hk; rewrite in_fset1U=> /orP[/eqP hki|] //.
    by move: hik; rewrite hki eqxx.
Qed.

(** Source for [finite_coordinate_split_join]: the inverse of psi is a
    right inverse when i is not in a, supporting Federer 2.6.6,
    p. 120. *)
Lemma finite_coordinate_split_join (x0 : X) (F : {fset I}) (i : I)
    (q : (finite_coordinate_space Y F * Y i)%type) :
  i \notin F -> finite_coordinate_split (finite_coordinate_join x0 q)=q.
Proof.
move=> hi; case: q=> v y.
rewrite /finite_coordinate_split /finite_coordinate_join /finite_coordinate_projection /=.
rewrite dfwithin; congr pair; apply: functional_extensionality_dep=> -[j hj] /=.
have hij : i != j by apply/eqP=> hij; move: hi; rewrite hij hj.
rewrite dfwithout // /finite_coordinate_section.
case: pselect=> h /=; last by exfalso; exact: h hj.
exact: finite_coordinate_coordinate_irrelevance.
Qed.

(** Source for [finite_coordinate_split_homeomorphism]: X_{a cup {i}}
    and X_a x X_i are homeomorphic through psi for i not in a,
    supporting the binary product method of Federer 2.6.4, p. 119,
    in 2.6.6, p. 120. *)
Theorem finite_coordinate_split_homeomorphism (x0 : X) (F : {fset I}) (i : I) :
  i \notin F ->
  continuous (@finite_coordinate_split F i) /\ continuous (@finite_coordinate_join x0 F i) /\
  (forall u : finite_coordinate_space Y (i |` F), finite_coordinate_join x0 (finite_coordinate_split u)=u) /\
  (forall q : (finite_coordinate_space Y F * Y i)%type, finite_coordinate_split (finite_coordinate_join x0 q)=q).
Proof.
move=> hi; split; first exact: finite_coordinate_split_continuous.
split; first exact: finite_coordinate_join_continuous.
split; first exact: finite_coordinate_join_split.
move=> q; exact: finite_coordinate_split_join.
Qed.
End Split.
