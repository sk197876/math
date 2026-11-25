(** Federer (1969), 3.4.5, p. 319: the analytic germ
    carrier and its ring operations, specified by representatives. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import RealNormUP NormMetric LocalGermUP LocalGermSealed AnalyticGermRepresentatives.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [analytic_germ_space]: the ring carrier of
    analytic germs at a in 3.4.5, p. 319. Its quotient
    representation is hidden by the local-germ interface. *)
Definition analytic_germ_space (R:realType) (X:lmodType R)
    (NX:X->R) (hNX:is_real_norm NX) (a:X):choiceType:=
  @LocalGerms.space (Topological.clone (real_norm_metric_space hNX) _) R
    (@analytic_representative_type R X NX hNX a)
    (@analytic_representative_value R X NX hNX a) a.

(** Source for [analytic_germ]: the representative-to-germ map
    of 3.4.5, p. 319. Only local values enter equality. *)
Definition analytic_germ (R:realType) (X:lmodType R)
    (NX:X->R) (hNX:is_real_norm NX) (a:X)
    (f:@analytic_representative_type R X NX hNX a):analytic_germ_space hNX a:=
  @LocalGerms.germ (Topological.clone (real_norm_metric_space hNX) _) R
    (@analytic_representative_type R X NX hNX a)
    (@analytic_representative_value R X NX hNX a) a f.

(** Source for [analytic_germ_zero]: the zero germ in
    the functional ring of 3.4.5, p. 319. *)
Definition analytic_germ_zero (R:realType) (X:lmodType R)
    (NX:X->R) (hNX:is_real_norm NX) (a:X):analytic_germ_space hNX a:=
  analytic_germ (@analytic_constant_representative R X NX hNX a 0).

(** Source for [analytic_germ_one]: the unit germ in
    the functional ring of 3.4.5, p. 319. *)
Definition analytic_germ_one (R:realType) (X:lmodType R)
    (NX:X->R) (hNX:is_real_norm NX) (a:X):analytic_germ_space hNX a:=
  analytic_germ (@analytic_constant_representative R X NX hNX a 1).

(** Source for [is_analytic_germ_operations]: addition, negation
    and multiplication in 3.4.5, p. 319, specified
    by their original representative equations before existence. *)
Record is_analytic_germ_operations (R:realType) (X:lmodType R)
    (NX:X->R) (hNX:is_real_norm NX) (a:X)
    (add mul:analytic_germ_space hNX a->analytic_germ_space hNX a->analytic_germ_space hNX a)
    (opp:analytic_germ_space hNX a->analytic_germ_space hNX a):Prop:={
  (** Source for [analytic_germ_add_equation]: functional addition
      induces germ addition, 3.4.5, p. 319. *)
  analytic_germ_add_equation:forall f g,
    add (analytic_germ f) (analytic_germ g)=analytic_germ (@analytic_add_representatives R X NX hNX a f g);
  (** Source for [analytic_germ_multiply_equation]: functional
      multiplication induces germ multiplication, 3.4.5, p. 319. *)
  analytic_germ_multiply_equation:forall f g,
    mul (analytic_germ f) (analytic_germ g)=analytic_germ (@analytic_multiply_representatives R X NX hNX a f g);
  (** Source for [analytic_germ_negate_equation]: functional negation
      induces germ negation, 3.4.5, p. 319. *)
  analytic_germ_negate_equation:forall f,
    opp (analytic_germ f)=analytic_germ (@analytic_negate_representative R X NX hNX a f)
}.
