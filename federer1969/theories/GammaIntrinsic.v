(** Federer, Geometric measure theory (1969); page numbers are printed book
    pages. Scalar fields, generalisations and exceptional cases are governed
    by the explicit hypotheses below. Supporting steps are distinguished
    from statements printed in the book. Erratum reference:
    docs/references/federer-erratum.tex (May 1987), cited by erratum page
    and book page/line. *)

From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import DualExterior.
From Federer Require Import Gamma GammaPower TraceDefinition.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Federer 1.4.5: Gamma is natural, so its formula is independent
    of the dual basic sequences used to compute it. *)
(** Source for [Gamma_basis_independent]: Federer (1969), 1.4.5, p. 20,
    natural Hom-tensor isomorphism and dual-basis formula for Gamma. In
    words: For finite-dimensional V, the inverse Gamma of the Hom-tensor
    identification sends f to the sum of each dual basic covector tensored
    with the image of its basis vector. Formalises the indicated part of the
    passage under the hypotheses in the statement below. *)
Theorem Gamma_basis_independent (K : fieldType) (V W : lmodType K)
    (I J : finType) (e : I -> V) (d : J -> V)
    (he : is_basis e) (hd : is_basis d) f :
  @Gamma K V W I e he f = @Gamma K V W J d hd f.
Proof.
apply (can_inj (@Gamma_inverseK K V W I e he)).
by rewrite !GammaK.
Qed.
(** Source for [Gamma_m_basis_independent]: Federer (1969), 1.4.5, p. 20,
    natural Hom-tensor isomorphism and dual-basis formula for Gamma. In
    words: For finite-dimensional V, the inverse Gamma of the Hom-tensor
    identification sends f to the sum of each dual basic covector tensored
    with the image of its basis vector. Formalises the indicated part of the
    passage under the hypotheses in the statement below. *)
Theorem Gamma_m_basis_independent (K : fieldType) (V W : lmodType K) m
    (I J : finType) (e : I -> exterior_power V m) (d : J -> exterior_power V m)
    (he : is_basis e) (hd : is_basis d) f :
  @Gamma_m K V W m I e he f = @Gamma_m K V W m J d hd f.
Proof.
apply (can_inj (@Gamma_m_inverseK K V W m I e he)).
by rewrite !Gamma_mK.
Qed.
(** Source for [trace_basis_independent]: Federer (1969), 1.4.5, p. 20,
    natural Hom-tensor isomorphism and dual-basis formula for Gamma. In
    words: For finite-dimensional V, the inverse Gamma of the Hom-tensor
    identification sends f to the sum of each dual basic covector tensored
    with the image of its basis vector. Formalises the indicated part of the
    passage under the hypotheses in the statement below. *)
Theorem trace_basis_independent (K : fieldType) (h2 : (1+1 : K) != 0)
    (V : lmodType K) (I J : finType) (e : I -> V) (d : J -> V)
    (he : is_basis e) (hd : is_basis d) f :
  @trace_Hom K h2 V I e he f = @trace_Hom K h2 V J d hd f.
Proof.
change (trace h2 V (@Gamma_include K h2 V V (@Gamma K V V I e he f)) =
  trace h2 V (@Gamma_include K h2 V V (@Gamma K V V J d hd f))).
by rewrite (Gamma_basis_independent he hd).
Qed.
