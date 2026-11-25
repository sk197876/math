(** Federer (1969), 4.1.5, p. 349: the original
    gauge is on K(U)+. Restricting the actual test values
    to U, or extending a scalar majorant by zero, gives
    exactly the same admissible tests and supremum.
    No Borel variation measure is substituted. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets reals constructive_ereal topology.
From Federer Require Import Hom RealNormUP OpenSubspaceExtension DistributionVariationUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section DistributionVariationDomain.
Variable R:realType.
Variable X:topologicalType.
Variable U:set X.
Variable Y:lmodType R.
Variable NY:Y->R.
Hypothesis hNY:is_real_norm NY.
Variable E:lmodType R.
Variable value:Hom E (GRing.Lmodule.clone R (X->Y) _).

(** Source for [distribution_domain_values_fun]: the original
    test values on U used by the first supremum in Federer
    4.1.5, p. 349. *)
Definition distribution_domain_values_fun (phi:E) (x:set_type U):Y:=
  value phi (set_val x).

(** Source for [distribution_domain_values_linear]: pointwise
    linearity of original test values on U, supporting the
    gauge of Federer 4.1.5, p. 349. *)
Lemma distribution_domain_values_linear:linear distribution_domain_values_fun.
Proof.
move=>c f g; apply:funext=>x.
exact:(congr1 (fun F:X->Y=>F (set_val x)) (linearP value c f g)).
Qed.

(** Source for [distribution_domain_values]: the original
    evaluation Hom on U, for the independent gauge of
    Federer 4.1.5, p. 349. *)
Definition distribution_domain_values:
    Hom E (GRing.Lmodule.clone R (set_type U->Y) _):=
  @HomMap R E (GRing.Lmodule.clone R (set_type U->Y) _)
    distribution_domain_values_fun (introT (asboolP _) distribution_domain_values_linear).

Hypothesis hOutside:forall phi:E,forall x:X,~U x ->value phi x=0.

(** Source for [distribution_domain_gauge_admissible]:
    the original pointwise bound on U is exactly the
    ambient bound by the zero-extended compact scalar test,
    for Federer 4.1.5, p. 349. *)
Lemma distribution_domain_gauge_admissible (phi:E) (f:set_type U->R):
  (forall x,NY (distribution_domain_values phi x)<=f x) <->
  (forall x,NY (value phi x)<=@open_extension R X U f x).
Proof.
split.
- move=>h x; case:(pselect (U x))=>hx.
  + pose z:set_type U:=exist _ x (mem_set hx).
    have hz:=h z.
    by rewrite -[x]/(set_val z) open_extensionE.
  + by rewrite (@hOutside phi x hx) (real_seminorm_zero hNY.1)
      (@open_extension_out R X U f x hx).
- move=>h x; have hx:=h (set_val x).
  by rewrite open_extensionE in hx.
Qed.

Variable S:Hom E R^o.

(** Source for [distribution_domain_gauge_values]: the two
    presentations have exactly the original supremum set,
    preserving Federer's definition in 4.1.5, p. 349. *)
Theorem distribution_domain_gauge_values (f:set_type U->R):
  distribution_variation_values NY distribution_domain_values S f=
    distribution_variation_values NY value S (@open_extension R X U f).
Proof.
apply:funext=>a; apply:propext; split=>-[phi [hNorm hValue]]; exists phi; split=>//.
- exact:(distribution_domain_gauge_admissible phi f).1 hNorm.
- exact:(distribution_domain_gauge_admissible phi f).2 hNorm.
Qed.

(** Source for [distribution_domain_gauge_value]: the original
    supremum and every finite-gauge assertion are unchanged
    by scalar zero extension, Federer 4.1.5, p. 349.
    The statement includes infinite gauge values. *)
Theorem distribution_domain_gauge_value (f:set_type U->R) c:
  is_distribution_variation_value NY distribution_domain_values S f c <->
    is_distribution_variation_value NY value S (@open_extension R X U f) c.
Proof.
by rewrite /is_distribution_variation_value distribution_domain_gauge_values.
Qed.
End DistributionVariationDomain.
