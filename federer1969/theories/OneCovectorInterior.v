(** Federer (1969), 4.1.6, p. 354: contraction
    of a positive-degree multivector by a one-covector
    has the preceding degree. The original operation
    is retained; only (p+1)-1=p is identified. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions.
From Federer Require Import Hom Bilinear GradedComponents ExteriorGrading AlternatingForms
  ExteriorHomogeneousProducts Alternating AlternatingExtension LeftInterior LeftInteriorHom.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [positive_one_covector_interior]: the
    original xi contracted by alpha used in the
    divergence formula, Federer 4.1.6,
    p. 354, with its actual preceding degree. *)
Definition positive_one_covector_interior (K:fieldType) (h2:(1+1:K)!=0)
    (V:lmodType K) p (xi:exterior_power V p.+1) (a:A_m V K^o 1):exterior_power V p:=
  exterior_reindex (subn1 p.+1) (left_interior h2 (ltn0Sn p) xi a).

(** Source for [positive_one_covector_interior_value]:
    identifying the natural-number degrees changes no
    underlying vector, supporting Federer
    4.1.6, p. 354. *)
Lemma positive_one_covector_interior_value (K:fieldType) (h2:(1+1:K)!=0)
    (V:lmodType K) p (xi:exterior_power V p.+1) (a:A_m V K^o 1):
  component_val (positive_one_covector_interior h2 xi a)=
    left_interior_hom h2 (component_val xi) (AlternatingExtension.form_homogeneous a).
Proof. by rewrite /positive_one_covector_interior exterior_reindexE left_interiorE. Qed.

(** Source for [positive_one_covector_interior_bilinear]:
    the original interior product remains bilinear,
    Federer 4.1.6, p. 354. *)
Lemma positive_one_covector_interior_bilinear (K:fieldType) (h2:(1+1:K)!=0)
    (V:lmodType K) p:bilinear (@positive_one_covector_interior K h2 V p).
Proof.
split.
- move=>a c x y; rewrite /positive_one_covector_interior
    ((@left_interior_bilinear K h2 V 1 p.+1 (ltn0Sn p)).1).
  exact:linearP.
- move=>x c a b; rewrite /positive_one_covector_interior
    ((@left_interior_bilinear K h2 V 1 p.+1 (ltn0Sn p)).2).
  exact:linearP.
Qed.
