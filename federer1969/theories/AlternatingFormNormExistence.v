(** Federer (1969), 4.1.6, p. 352: existence of the
    actual induced norm for arbitrary normed coefficients.
    The previous finite bound embeds the original forms
    into the sealed continuous multilinear space. Its
    exact norm pulls back along a linear injection. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions reals.
From Federer Require Import Hom RealNormUP RealSeminormOperations AlternatingForms
  AlternatingPairing AlternatingFormNormBound AlternatingFormNormUP
  InnerProductUP InnerNorm HilbertFormCompactness LinearBasis
  ContinuousMultilinearUP ContinuousMultilinearSealed ContinuousMultilinearNorm.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [alternating_form_norm_exists]: the norm
    chosen by the method of 3.1.11 exists on all
    the original A^m(R^n,W), Federer 4.1.6,
    p. 352. No coefficient completeness or dimension
    hypothesis is imposed. *)
Theorem alternating_form_norm_exists (R:realType) (h2:(1+1:R)!=0)
    (V W:lmodType R) (B:V->V->R) (hB:is_inner_product B)
    n (e:'I_n->V) (he:is_basis e) (NW:W->R) (hNW:is_real_norm NW) m:
  exists N:A_m V W m->R,is_real_norm N /\is_alternating_form_norm (inner_norm hB) NW N.
Proof.
pose NV:=inner_norm hB.
pose hNV:=inner_norm_real_norm hB.
pose Z:=@ContinuousMultilinear.space R m V W NV NW hNV hNW.
pose ev:=@ContinuousMultilinear.evaluation R m V W NV NW hNV hNW.
pose NZ:=@ContinuousMultilinear.norm R m V W NV NW hNV hNW.
have hZ:=@ContinuousMultilinear.laws R m V W NV NW hNV hNW.
have hFull (phi:A_m V W m):exists z:Z,forall u,ev u z=form_ordered_value phi u.
  exact:(continuous_multilinear_surjective hZ
    (@finite_source_alternating_form_bounded R h2 V W B hB n e he NW hNW m phi)).
pose J:=fun phi:A_m V W m=>proj1_sig (cid (hFull phi)).
have hJE phi u:ev u (J phi)=form_ordered_value phi u.
  exact:(proj2_sig (cid (hFull phi))).
have hLinear:linear J.
  move=>c phi psi; apply:(continuous_multilinear_extensional hZ)=>u.
  rewrite hJE linearP /= !hJE.
  exact:(linearP (@form_ordered_evaluation R V W m u) c phi psi).
have hInjective:injective J.
  move=>phi psi hEqual; apply:form_ext=>t.
  have hValue:=congr1 (fun z=>ev [ffun i=>tnth t i] z) hEqual.
  by rewrite !hJE !form_ordered_value_tuple in hValue.
pose L:Hom (A_m V W m) Z:=@HomMap R _ _ J (introT (asboolP _) hLinear).
exists (fun phi=>NZ (L phi)); split.
- exact:(@real_norm_injective_precompose R _ Z NZ
    (continuous_multilinear_norm_is_norm hNW hZ) (hom_as_linear L) hInjective).
- move=>phi.
  have hNorm:=continuous_multilinear_norm_laws hZ (L phi).
  have hFunction:(fun u=>ev u (L phi))=form_ordered_value phi.
    apply:funext=>u; exact:hJE.
  by rewrite hFunction in hNorm.
Qed.
