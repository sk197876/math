(** Federer (1969), 4.1.7, p. 356: the
    characteristic pairing for contraction by a
    one-covector. The actual left interior from
    1.5.1, pp. 21–22, is preserved. *)
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import AlternatingSum BoundedHom HomogeneousHom GradedComponents Hom ExteriorGrading ExteriorHomogeneousProducts AlternatingForms AlternatingPairing
  AlternatingProduct ScalarCoefficients LeftInterior LeftInteriorHom OneCovectorInterior CurrentVectorContraction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [current_positive_interior_pairing]: the
    pairing of xi contracted alpha with psi
    equals the pairing of xi with alpha
    wedge psi, supporting Federer 4.1.7,
    p. 356. Only equal degrees are identified. *)
Theorem current_positive_interior_pairing (K:fieldType) (h2:(1+1:K)!=0)
    (V:lmodType K) p (xi:exterior_power V p.+1) (alpha:A_m V K^o 1) (psi:A_m V K^o p):
  pairing (positive_one_covector_interior h2 xi alpha) psi=
    form_include (form_wedge h2 (scalar_bilinear K) alpha psi) (component_val xi).
Proof.
pose z:=exterior_reindex (esym (add1n p)) xi.
have hZ:component_val z=component_val xi:=
  @exterior_reindexE K V p.+1 (1+p) (esym (add1n p)) xi.
have hSame:@current_vector_contraction K h2 V 1 p z alpha=
    positive_one_covector_interior h2 xi alpha.
  apply:val_inj.
  have hLeft:component_val (@current_vector_contraction K h2 V 1 p z alpha)=
      left_interior_hom h2 (component_val z) (AlternatingExtension.form_homogeneous alpha).
    by rewrite /current_vector_contraction exterior_reindexE left_interiorE.
  apply:(eq_trans hLeft).
  apply:(eq_trans (congr1 (fun t=>left_interior_hom h2 t
    (AlternatingExtension.form_homogeneous alpha)) hZ)).
  exact:esym (positive_one_covector_interior_value h2 xi alpha).
have hPair:=@current_vector_contraction_pairing K h2 V 1 p z alpha psi.
have hSamePair:=congr1 (fun t:exterior_power V p=>pairing t psi) hSame.
exact (eq_trans (esym hSamePair) (eq_trans hPair
  (congr1 (fun t=>form_include (form_wedge h2 (scalar_bilinear K) alpha psi) t) hZ))).
Qed.
