(** Federer (1969), 2.6.6, pp. 120–121, final paragraph: the argument
    applies to inverse limits of consistent Daniell integrals on compact
    Hausdorff spaces. This file specifies a directed inverse system by its
    bonding-map laws. The directed index set is nonempty, the usual
    convention. Maps need not be onto. Normalized monotone functionals
    retain the standing hypotheses of the product discussion. *)
From mathcomp Require Import all_boot classical_sets topology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [is_directed_preorder]: supporting directed index
    structure for the arbitrary inverse limits in Federer 2.6.6,
    pp. 120–121. Antisymmetry is unnecessary. *)
Record is_directed_preorder (I : Type) (le : I -> I -> Prop) : Prop := {
  (** Source for [directed_preorder_nonempty]: nonempty index
      convention supporting the inverse-limit paragraph, Federer
      2.6.6, pp. 120–121. *)
  directed_preorder_nonempty : exists i : I, True;
  (** Source for [directed_preorder_reflexive]: reflexivity of
      the index relation, supporting Federer 2.6.6, pp. 120–121. *)
  directed_preorder_reflexive : forall i, le i i;
  (** Source for [directed_preorder_transitive]: transitivity of
      the index relation, supporting Federer 2.6.6, pp. 120–121. *)
  directed_preorder_transitive : forall i j k, le i j -> le j k -> le i k;
  (** Source for [directed_preorder_upper]: common upper indices,
      supporting the finite compatibility arguments in Federer
      2.6.6, pp. 120–121. *)
  directed_preorder_upper : forall i j, exists k, le i k /\ le j k
}.

(** Source for [is_compact_inverse_system]: abstract bonding-map
    specification for the compact Hausdorff inverse systems in the
    final paragraph of Federer 2.6.6, pp. 120–121. *)
Record is_compact_inverse_system (I : choiceType) (le : I -> I -> Prop)
    (Y : I -> topologicalType) (b : forall i j, Y j -> Y i) : Prop := {
  (** Source for [compact_inverse_system_directed]: directedness
      of the system, supporting Federer 2.6.6, pp. 120–121. *)
  compact_inverse_system_directed : is_directed_preorder le;
  (** Source for [compact_inverse_system_compact]: compact factors,
      as in Federer 2.6.6, pp. 120–121. *)
  compact_inverse_system_compact : forall i, compact (@setT (Y i));
  (** Source for [compact_inverse_system_hausdorff]: Hausdorff
      factors, as in Federer 2.6.6, pp. 120–121. *)
  compact_inverse_system_hausdorff : forall i, hausdorff_space (Y i);
  (** Source for [compact_inverse_system_continuous]: continuous
      bonding maps, supporting Federer 2.6.6, pp. 120–121. *)
  compact_inverse_system_continuous : forall i j, le i j -> continuous (b i j);
  (** Source for [compact_inverse_system_identity]: identity
      bonding-map law, supporting Federer 2.6.6, pp. 120–121. *)
  compact_inverse_system_identity : forall i x, b i i x=x;
  (** Source for [compact_inverse_system_composition]: bonding-map
      composition law, supporting Federer 2.6.6, pp. 120–121. *)
  compact_inverse_system_composition : forall i j k, le i j -> le j k ->
    forall x, b i j (b j k x)=b i k x
}.
