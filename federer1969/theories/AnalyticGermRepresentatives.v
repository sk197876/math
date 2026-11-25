(** Federer (1969), 3.4.5, p. 319: actual analytic
    representatives of the local ring. Rocq functions are total;
    the analytic witness uses only an open neighbourhood in the
    original domain. Enlarging the outer domain to the whole
    carrier changes neither that witness nor the resulting germ. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP NormOpenDomainLaws
  NormAnalyticUP NormAnalyticDomain NormAnalyticArithmeticLocal NormAnalyticConstant
  AnalyticGermNeighbourhood.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section Representatives.
Variable R:realType.
Variable X:lmodType R.
Variable NX:X->R.
Hypothesis hNX:is_real_norm NX.
Variable a:X.
Local Notation N:=(fun t:R^o=>`|t|).
Local Notation hN:=(@scalar_absolute_value_norm R).
Local Notation AN f:=(@norm_analytic_at R X R^o NX N hNX hN setT f a).

(** Source for [analytic_germ_representative]: the real-valued
    functions analytic at a, 3.4.5, p. 319. The proof
    records actual neighbourhood regularity, without a chosen Taylor series. *)
Definition analytic_germ_representative:={f:X->R | AN f}.

(** Source for [analytic_representative_type]: the background
    choice structure for representatives in 3.4.5, p. 319;
    it supplies no analytic or algebraic assertion. *)
Definition analytic_representative_type:choiceType:=
  [the choiceType of {classic analytic_germ_representative}].

(** Source for [analytic_representative_value]: the actual
    represented function in 3.4.5, p. 319. *)
Definition analytic_representative_value (f:analytic_representative_type):X->R:=proj1_sig f.

(** Source for [analytic_representative_analytic]: the representative
    is analytic at its original centre, 3.4.5, p. 319. *)
Lemma analytic_representative_analytic (f:analytic_representative_type):
  AN (analytic_representative_value f).
Proof. exact:proj2_sig f. Qed.

(** Source for [analytic_representative_from_domain]: an actual
    partial-domain analytic function defines a representative of the
    same germ, 3.4.5, p. 319. No values outside its
    analytic neighbourhood enter the proof. *)
Lemma analytic_representative_from_domain (A:set X) (f:X->R):
  @norm_analytic_at R X R^o NX N hNX hN A f a ->
  exists p:analytic_representative_type,analytic_representative_value p=f.
Proof.
move=>hf;have hFull:=@norm_analytic_at_domain_enlargement R X R^o NX N hNX hN
  A setT f a (fun x hx=>Logic.I) hf.
by exists (exist _ f hFull).
Qed.

(** Source for [analytic_representative_constant]: constants
    represent the zero and unit germs in 3.4.5, p. 319. *)
Lemma analytic_representative_constant (c:R):AN (fun _=>c).
Proof.
exact:(@norm_constant_analytic R X R^o NX N hNX hN setT
  (fun x hx=>@norm_full_domain_interior R X NX x) c a Logic.I).
Qed.

(** Source for [analytic_representative_add]: analytic representatives
    are closed under functional addition, 3.4.5, p. 319. *)
Lemma analytic_representative_add (f g:analytic_representative_type):
  AN (fun x=>analytic_representative_value f x+analytic_representative_value g x).
Proof.
exact:(@norm_analytic_at_common_domain_add R X R^o NX N hNX hN setT
  _ _ a (analytic_representative_analytic f) (analytic_representative_analytic g)).
Qed.

(** Source for [analytic_representative_negate]: functional negation
    preserves the representatives of 3.4.5, p. 319. *)
Lemma analytic_representative_negate (f:analytic_representative_type):
  AN (fun x=> -analytic_representative_value f x).
Proof.
exact:(@norm_analytic_at_negate R X R^o NX N hNX hN setT
  _ a (analytic_representative_analytic f)).
Qed.

(** Source for [analytic_representative_multiply]: functional multiplication
    preserves the representatives of 3.4.5, p. 319. *)
Lemma analytic_representative_multiply (f g:analytic_representative_type):
  AN (fun x=>analytic_representative_value f x*analytic_representative_value g x).
Proof.
have hh:=@analytic_germ_product_at R X NX hNX setT setT _ _ a
  (analytic_representative_analytic f) (analytic_representative_analytic g).
exact:(@norm_analytic_at_domain_enlargement R X R^o NX N hNX hN
  (setT `&` setT) setT _ a (fun x hx=>Logic.I) hh).
Qed.
End Representatives.

(** Source for [analytic_constant_representative]: constant
    representatives for the zero and unit in 3.4.5, p. 319. *)
Definition analytic_constant_representative (R:realType) (X:lmodType R)
    (NX:X->R) (hNX:is_real_norm NX) (a:X) (c:R):
    @analytic_representative_type R X NX hNX a:=
  exist _ (fun _=>c) (@analytic_representative_constant R X NX hNX a c).

(** Source for [analytic_add_representatives]: addition of the
    actual analytic representatives in 3.4.5, p. 319. *)
Definition analytic_add_representatives (R:realType) (X:lmodType R)
    (NX:X->R) (hNX:is_real_norm NX) (a:X)
    (f g:@analytic_representative_type R X NX hNX a):
    @analytic_representative_type R X NX hNX a:=
  exist _ (fun x=>analytic_representative_value f x+analytic_representative_value g x)
    (@analytic_representative_add R X NX hNX a f g).

(** Source for [analytic_negate_representative]: negation of the
    actual analytic representatives in 3.4.5, p. 319. *)
Definition analytic_negate_representative (R:realType) (X:lmodType R)
    (NX:X->R) (hNX:is_real_norm NX) (a:X)
    (f:@analytic_representative_type R X NX hNX a):
    @analytic_representative_type R X NX hNX a:=
  exist _ (fun x=> -analytic_representative_value f x)
    (@analytic_representative_negate R X NX hNX a f).

(** Source for [analytic_multiply_representatives]: multiplication
    of the actual analytic representatives in 3.4.5, p. 319. *)
Definition analytic_multiply_representatives (R:realType) (X:lmodType R)
    (NX:X->R) (hNX:is_real_norm NX) (a:X)
    (f g:@analytic_representative_type R X NX hNX a):
    @analytic_representative_type R X NX hNX a:=
  exist _ (fun x=>analytic_representative_value f x*analytic_representative_value g x)
    (@analytic_representative_multiply R X NX hNX a f g).
