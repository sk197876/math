(** Federer (1969), 4.1.26, p. 383: the
    degree is the original signed numerical sum
    of determinant signs over A intersect f^-1{y}.
    The source summand is zero off A, so
    the full fibre expresses exactly that restriction.
    Undefined or infinite sums are not assigned
    finite real values; almost-everywhere existence is
    a separate theorem. *)
From mathcomp Require Import all_boot all_order all_algebra
  classical_sets reals constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct
  ExtendedRealOrderTopology PartialFunctionUP PartialFunctionPostcomposition
  PartialFunctionExtensionality PartialFibreNumericalSum LipschitzDegreeSummandSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [is_lipschitz_degree]: independently specify
    the original finite signed fibre sum in
    4.1.26, p. 383. Boundedness, measurability,
    the current identity and almost-everywhere domain
    are proved later, not inserted as axioms. *)
Definition is_lipschitz_degree (R:realType) m
    (f:R_n R m->R_n R m) (A:set (R_n R m))
    (d:partial_function (R_n R m) R):Prop:=
  forall y a,partial_function_graph d y a<->
    partial_function_graph
      (partial_fibre_numerical_sum f (partial_function_postcompose
        (@LipschitzDegreeSummand.value R m f A)
        (fun s:R=>(s%:E:extended_real_line R)))) y a%:E.

(** Source for [lipschitz_degree_unique]: the original
    signed degree has one partial graph,
    supporting 4.1.26, p. 383. No
    outside-domain representative is exposed. *)
Theorem lipschitz_degree_unique (R:realType) m f A
    (d e:partial_function (R_n R m) R):
  is_lipschitz_degree f A d->is_lipschitz_degree f A e->d=e.
Proof.
move=>hD hE;apply:partial_function_graph_extensionality=>y a.
by rewrite (hD y a) (hE y a).
Qed.
