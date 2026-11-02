(** Local degree-zero corrections to Federer (1969), 1.6.3, p. 24. These
    corrections are not entries in Federer's erratum. *)

From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import SimpleVectors SimpleCovectors CovectorDimension.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

Section Boundary.
Variable K : fieldType.
Hypothesis h2 : (1+1 : K) != 0.
Variable V : lmodType K.

(** Source for [scalar_covector]: Federer 1.6.3, p. 24, empty-product
    boundary of the definition. Supporting construction of a scalar
    zero-covector, using Omega to identify the zeroth powers. *)
Definition scalar_covector (c : K) : A_m V K^o 0 :=
  Omega_m h2 (exterior_zeroth_inclusion (Hom V K^o) c).

(** Source for [scalar_covector_include]: Federer 1.6.3, p. 24,
    degree-zero convention. Supporting identification: the scalar
    covector includes in the graded algebra as the constant form. *)
Lemma scalar_covector_include c :
  form_include (scalar_covector c) = coefficient_form V (c : K^o).
Proof.
rewrite /scalar_covector Omega_m_include zeroth_inclusion_val /exterior_scalar
  linearZ /Omega Omega_W_one.
rewrite -linearZ; congr (coefficient_form V _); exact: mulr1.
Qed.

(** Source for [omega_lambda_empty]: Federer 1.6.3, p. 24, literal
    definition of simplicity. Supporting boundary identity: an empty
    indexed product of one-covectors is the scalar covector one. *)
Lemma omega_lambda_empty n (omega : 'I_n -> A_m V K^o 1)
  (lambda : Lambda n 0) : omega_lambda h2 omega lambda = scalar_covector 1.
Proof.
apply: (can_inj (@form_includeK K V K^o 0)).
by rewrite omega_lambda_include (tuple0 (val lambda)) scalar_covector_include.
Qed.

(** Source for [scalar_covector_simple]: Federer 1.6.3, p. 24, first
    sentence. Direct consequence of its literal definition: a scalar
    zero-covector is simple exactly when its scalar is one. *)
Theorem scalar_covector_simple c : simple_covector h2 (scalar_covector c) <-> c = 1.
Proof.
rewrite /scalar_covector simple_covector_Omega simple_zero_iff.
split=> [h|->] //.
exact: (can_inj (exterior_zeroth_inclusionK (Hom V K^o))) h.
Qed.

(** Source for [scalar_covector_nonzero]: Federer 1.6.3, p. 24,
    nonzero hypothesis of the dimension assertion. Supporting lemma
    for the explicit degree-zero counterexample. *)
Lemma scalar_covector_nonzero c : c != 0 -> scalar_covector c != 0.
Proof.
move=> hc; apply/eqP=> h.
have hz : exterior_zeroth_inclusion (Hom V K^o) c = 0.
  apply: Omega_m_injective; by rewrite linear0.
by move: (@scalar_mvector_nonzero K (Hom V K^o) c hc); rewrite hz eqxx.
Qed.

(** Source for [scalar_covector_associated]: Federer 1.6.3, p. 24,
    displayed associated space. Supporting boundary calculation: the
    associated space of a nonzero scalar covector is the zero space. *)
Lemma scalar_covector_associated c : c != 0 -> forall a,
  covector_subspace h2 (scalar_covector c) a <-> a = 0.
Proof.
move=> hc a; rewrite /scalar_covector covector_associated_Omega.
exact: (@scalar_associated_zero K (Hom V K^o) c hc a).
Qed.

(** Source for [covector_dimension_zero_counterexample]: Federer 1.6.3, p.
    24, asserted equality iff simplicity. Local counterexample: the scalar 2
    is nonzero and has a zero-dimensional associated space, but is not the
    empty product 1. Characteristic different from two is explicit. *)
Theorem covector_dimension_zero_counterexample :
  exists phi : A_m V K^o 0,
    phi != 0 /\
    (forall a, covector_subspace h2 phi a <-> a = 0) /\
    ~ simple_covector h2 phi.
Proof.
exists (scalar_covector (1+1)); split; first exact: scalar_covector_nonzero h2.
split; first exact: scalar_covector_associated h2.
move/scalar_covector_simple=> h.
have h1 : (1 : K) = 0 by apply: (addrI (1 : K)); rewrite addr0.
by move: (oner_neq0 K); rewrite h1 eqxx.
Qed.
End Boundary.
