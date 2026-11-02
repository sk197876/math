(** Federer (1969), 2.6.6, p. 120: supporting coordinate replacement for
    finite products of the factor Daniell integrals. The product is
    specified by its marginal laws; these operations provide its existence
    proof by successive integrations, following the method of 2.6.4. Source
    context: CompactProductFiniteControl.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp mathcomp_extra classical_sets topology.
From Federer Require Import DependentProductContinuity TopologicalProductMaps.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

Section Replacement.
Variables (I : choiceType) (Y : I -> topologicalType).
Local Notation X := (prod_topology Y).

(** Source for [product_coordinate_replace]: supporting replacement
    of one coordinate for the finite integrations in Federer 2.6.6,
    p. 120. The dependent family permits different factor spaces. *)
Definition product_coordinate_replace (i : I) (p : Y i * X) : X :=
  dfwith p.2 i p.1.

(** Source for [product_coordinate_replace_continuous]: joint
    continuity of coordinate replacement, supporting the compact-section
    argument of Federer 2.6.4, p. 119, applied in 2.6.6, p. 120. *)
Lemma product_coordinate_replace_continuous (i : I) :
  continuous (product_coordinate_replace (i:=i)).
Proof.
apply: dependent_product_map_continuous=> j; case: (eqVneq i j)=> [<-|hij].
- have he : (fun q : Y i*X=>product_coordinate_replace q i)=fst.
    by apply: funext=> q; rewrite /product_coordinate_replace dfwithin.
  rewrite he; exact: first_projection_continuous.
- have he : (fun q : Y i*X=>product_coordinate_replace q j)=(fun q=>q.2 j).
    by apply: funext=> q; rewrite /product_coordinate_replace dfwithout.
  rewrite he=> p; exact: continuous_comp (@second_projection_continuous (Y i) X p) (@proj_continuous I Y j p.2).
Qed.

(** Source for [product_coordinate_replacements_commute]: distinct
    coordinate replacements commute, supporting consistency of finite
    products in Federer 2.6.6, p. 120. *)
Lemma product_coordinate_replacements_commute (i j : I) (u : Y i) (v : Y j) (x : X) :
  i != j -> dfwith (dfwith x i u) j v=dfwith (dfwith x j v) i u.
Proof.
move=> hij; have hji : j != i by rewrite eq_sym.
apply: functional_extensionality_dep=> k.
case: (eqVneq i k)=> [<-|hik].
- by rewrite [LHS]dfwithout // !dfwithin.
case: (eqVneq j k)=> [<-|hjk].
- by rewrite dfwithin [RHS]dfwithout // dfwithin.
by rewrite !dfwithout.
Qed.
(** Source for [product_coordinate_section_continuous]: a section
    varying one coordinate is continuous, supporting the integrations
    in Federer 2.6.6, p. 120. *)
Lemma product_coordinate_section_continuous (i : I) (x : X) :
  continuous (fun u : Y i=>(dfwith x i u : X)).
Proof.
have hp : continuous (fun u : Y i=>(u,x)).
  apply: topological_pair_continuous; [by move=> u|exact: cst_continuous].
move=> u; exact: continuous_comp (hp u) (@product_coordinate_replace_continuous i (u,x)).
Qed.
End Replacement.
