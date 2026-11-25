(** Federer (1969), 4.1.8, p. 360: uniqueness
    uses all separated mixed degrees. This supporting span
    theorem is a direct application of the original direct-sum
    exterior isomorphism, 1.3.2, p. 14, and the finite
    covector isomorphism Omega, 1.4.4, p. 20. *)
From mathcomp Require Import all_boot all_order all_algebra boolp.
From Federer Require Import BoundedHom HomogeneousHom GradedComponents Hom Bilinear AlgebraUP Tensor TensorUP
  TensorMaps GradedAlgebra GradedTensor UnitalGradedTensor LinearBasis
  ExteriorAlgebra ExteriorGrading ExteriorMaps ExteriorDirectSum ExteriorHomogeneousProducts
  AlternatingForms AlternatingSum AlternatingDual AlternatingProduct AlternatingUnit
  ScalarCoefficients OmegaConstruction OmegaNaturality OmegaFinite
  FormComponentEqualDegree CovectorBlockTensorImage.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section CovectorBlockSpan.
Variable K:fieldType.
Hypothesis h2:(1+1:K)!=0.
Variables V X Y W:lmodType K.
Variables (p:{linear V->X}) (q:{linear V->Y}) (P:{linear X->V}) (Q:{linear Y->V}).
Hypothesis hDecomposition:forall v,P (p v)+Q (q v)=v.
Variable N:nat.
Variable e:'I_N->V.
Hypothesis he:is_basis e.

(** Source for [covector_block_span]: a linear map on
    the original finite-dimensional d-covectors that vanishes
    on every separated mixed product is zero, supporting
    Federer 4.1.8, p. 360. The proof uses all
    pairs of degrees with sum d and includes d=0. *)
Theorem covector_block_span d (L:Hom (A_m V K^o d) W):
  (forall k l (h:(k+l)%N=d) (a:A_m X K^o k) (b:A_m Y K^o l),
    L (form_reindex h (form_wedge h2 (scalar_bilinear K) (A_m_dual p a) (A_m_dual q b)))=0)->
  forall phi,L phi=0.
Proof.
move=>hZero phi.
pose rX:=GRing.Linear.clone _ _ _ _ (@Hom_dual K X V (scalar_algebra K) P) _.
pose rY:=GRing.Linear.clone _ _ _ _ (@Hom_dual K Y V (scalar_algebra K) Q) _.
pose pDual:=GRing.Linear.clone _ _ _ _ (@Hom_dual K V X (scalar_algebra K) p) _.
pose qDual:=GRing.Linear.clone _ _ _ _ (@Hom_dual K V Y (scalar_algebra K) q) _.
have hDualDecomposition:forall f:Hom V K^o,pDual (rX f)+qDual (rY f)=f.
  move=>f;apply:hom_ext=>v.
  change (f (P (p v))+f (Q (q v))=f v).
  by rewrite -linearD hDecomposition.
pose C:Hom (A_star V K^o) (A_m V K^o d):=
  hom_of_linear (GRing.Linear.clone _ _ _ _ (@form_component K V K^o d) _).
pose G:=hom_comp L (hom_comp C (hom_of_linear (Omega h2 V))).
pose b:=@ExteriorDirectSum.beta K (Hom V K^o) (Hom X K^o) (Hom Y K^o) pDual qDual.
pose a:=@ExteriorDirectSum.alpha K h2 (Hom V K^o) (Hom X K^o) (Hom Y K^o) rX rY.
pose J:=hom_comp G (hom_of_linear b).
have hTensor:forall z,homogeneous
    (tensor_grading_product (exterior_grading (Hom X K^o)) (exterior_grading (Hom Y K^o))) d z->J z=0.
  apply:(@tensor_component_induction K (exterior_space (Hom X K^o)) (exterior_space (Hom Y K^o))
    (exterior_grading (Hom X K^o)) (exterior_grading (Hom Y K^o)) d (fun z=>J z=0)).
  - by rewrite linear0.
  - by move=>x y hx hy;rewrite (linD (hom_linear J) x y) hx hy add0r.
  - by move=>c x hx;rewrite (linZ (hom_linear J) c x) hx scaler0.
  - move=>k l x y hkl hx hy.
    pose xi:exterior_power (Hom X K^o) k:=Component (introT eqP hx).
    pose eta:exterior_power (Hom Y K^o) l:=Component (introT eqP hy).
    change (L (form_component d (Omega h2 V (b (tensor_inj x y))))=0).
    have hImage:=@covector_block_tensor_image K h2 V X Y p q k l xi eta.
    change (Omega h2 V (b (tensor_inj x y))=
      form_include (form_wedge h2 (scalar_bilinear K)
        (A_m_dual p (Omega_m h2 xi)) (A_m_dual q (Omega_m h2 eta)))) in hImage.
    rewrite hImage (@form_component_equal_degree K V K^o (k+l) d hkl).
    exact:(hZero k l hkl (Omega_m h2 xi) (Omega_m h2 eta)).
have [xi hXi]:=@Omega_m_finite_surjective K h2 V N e he d phi.
have hHomogeneous:=@alpha_graded K h2 (Hom V K^o) (Hom X K^o) (Hom Y K^o) rX rY
  d (component_val xi) (component_homogeneous xi).
have hValue:=hTensor (a (component_val xi)) hHomogeneous.
change (G (b (a (component_val xi)))=0) in hValue.
rewrite (@beta_alpha K h2 (Hom V K^o) (Hom X K^o) (Hom Y K^o)
  rX pDual rY qDual hDualDecomposition (component_val xi)) in hValue.
change (L (Omega_m h2 xi)=0) in hValue.
by rewrite hXi in hValue.
Qed.
End CovectorBlockSpan.
